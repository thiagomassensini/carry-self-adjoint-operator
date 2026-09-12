import CarrySelfAdjointOperator.CompletedC3GreenFrameOrientedCarrier
import CarrySelfAdjointOperator.CompletedNativePolarizedTfvdGreenMomentKernel
import CPFormal.Analytic.CpNativeGpreFiniteGluedGreenDefect
import CPFormal.Analytic.CpNativeGpreHilbertGluedGreenDefect
import CPFormal.Analytic.CpNativeGpreTfvdCanonicalGluing
import Mathlib.Tactic

/-!
# Completed native Hilbert trace glue and the mixed Wronskian

The native G_pre construction already carries the vertical edge core and its
provenance boundary coordinates in one Hilbert boundary. This file exposes
that identity with the exact coordinate orientation used by the current
Green--Wronskian ledger.

The result is deliberately a trace-glue result. It does not identify the
finite C3 scalar readout with a native edge-core state, and it does not make
the existing C3 structural or completion residual disappear. Those are
separate crosswalks: the present API proves the native Hilbert cancellation
for an actual edge core, while the C3 scalar ledger still needs a canonical
state map and a defect/source relation.
-/

open scoped ComplexConjugate InnerProduct lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-! ## Native finite Hilbert trace glue -/

/-- Division-free Green defect in the finite native Hilbert boundary carrier. -/
def canonicalNativeFiniteGluedHilbertTraceGreenDefect
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x y : NativeGpreComplexEdgeCore) : ℂ :=
  inner ℂ
      ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).fluxTrace y)
      ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).valueTrace x) -
    inner ℂ
      ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).valueTrace y)
      ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).fluxTrace x)

/-- The finite glued Hilbert defect is exactly the vertical Wronskian. The
provenance coordinates are retained in both traces and cancel by their
Green-symmetry theorem. -/
theorem canonicalNativeFiniteGluedHilbertTraceGreenDefect_eq_verticalWronskian
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x y : NativeGpreComplexEdgeCore) :
    canonicalNativeFiniteGluedHilbertTraceGreenDefect q S x y =
      carryWeightedVerticalBoundaryWronskian q
        (nativeGpreCanonicalVerticalRealization x)
        (nativeGpreCanonicalVerticalRealization y) := by
  exact nativeGpreFiniteGluedHilbertGreenDefect_eq_verticalWronskian
    q S x y

/-- Coordinate form of the preceding identity, including the exact
conjugation and order of the two edge states. -/
theorem canonicalNativeFiniteGluedHilbertTraceGreenDefect_eq_coordinateWronskian
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x y : NativeGpreComplexEdgeCore) :
    canonicalNativeFiniteGluedHilbertTraceGreenDefect q S x y =
      (q : ℂ)⁻¹ *
        ((starRingEnd ℂ) (y 1) * x 0 -
          (starRingEnd ℂ) (y 0) * x 1) := by
  rw [canonicalNativeFiniteGluedHilbertTraceGreenDefect_eq_verticalWronskian]
  rfl

/-- The full vertical-space version of the same trace-glue identity. -/
def canonicalNativeHilbertGluedTraceGreenDefect
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x y : CarryVerticalL2) : ℂ :=
  inner ℂ
      ((nativeGpreHilbertGluedBoundaryPencil q S).fluxTrace y)
      ((nativeGpreHilbertGluedBoundaryPencil q S).valueTrace x) -
    inner ℂ
      ((nativeGpreHilbertGluedBoundaryPencil q S).valueTrace y)
      ((nativeGpreHilbertGluedBoundaryPencil q S).fluxTrace x)

/-- The full Hilbert gluing has the same vertical Wronskian, with no
compression of its provenance coordinates. -/
theorem canonicalNativeHilbertGluedTraceGreenDefect_eq_verticalWronskian
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x y : CarryVerticalL2) :
    canonicalNativeHilbertGluedTraceGreenDefect q S x y =
      carryWeightedVerticalBoundaryWronskian q x y := by
  exact nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian q S x y

/-- Explicit coordinate form for the full Hilbert gluing. -/
theorem canonicalNativeHilbertGluedTraceGreenDefect_eq_coordinateWronskian
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x y : CarryVerticalL2) :
    canonicalNativeHilbertGluedTraceGreenDefect q S x y =
      (q : ℂ)⁻¹ *
        ((starRingEnd ℂ) (y 1) * x 0 -
          (starRingEnd ℂ) (y 0) * x 1) := by
  rw [canonicalNativeHilbertGluedTraceGreenDefect_eq_verticalWronskian]
  rfl

/-! ## Scalar trace coordinates and orientation -/

/-- The scalar wedge with the native value/flux trace coordinates. The
leading minus sign is intentional: mixedScalarBoundaryWedge orders its two
legs oppositely to the native vertical Wronskian. -/
def canonicalNativeVerticalTraceBoundaryWedge
    (q : ℝ) (x y : NativeGpreComplexEdgeCore) : ℂ :=
  - mixedScalarBoundaryWedge
      (x 0) ((q : ℂ)⁻¹ * x 1 - x 0)
      (y 0) ((q : ℂ)⁻¹ * y 1 - y 0)

/-- The native scalar trace wedge is exactly the vertical Wronskian. -/
theorem canonicalNativeVerticalTraceBoundaryWedge_eq_verticalWronskian
    (q : ℝ) (x y : NativeGpreComplexEdgeCore) :
    canonicalNativeVerticalTraceBoundaryWedge q x y =
      carryWeightedVerticalBoundaryWronskian q
        (nativeGpreCanonicalVerticalRealization x)
        (nativeGpreCanonicalVerticalRealization y) := by
  unfold canonicalNativeVerticalTraceBoundaryWedge
    mixedScalarBoundaryWedge
    carryWeightedVerticalBoundaryWronskian
  simp only [nativeGpreCanonicalVerticalRealization_apply]
  simp only [map_sub, map_mul, map_inv₀]
  simp
  ring

/-- The scalar wedge in the opposite orientation is the negative native
vertical Wronskian. This is the precise orientation mismatch that must be
handled before comparing a C3 mixed scalar readout. -/
theorem mixedScalarBoundaryWedge_nativeTrace_eq_neg_verticalWronskian
    (q : ℝ) (x y : NativeGpreComplexEdgeCore) :
    mixedScalarBoundaryWedge
        (x 0) ((q : ℂ)⁻¹ * x 1 - x 0)
        (y 0) ((q : ℂ)⁻¹ * y 1 - y 0) =
      - carryWeightedVerticalBoundaryWronskian q
        (nativeGpreCanonicalVerticalRealization x)
        (nativeGpreCanonicalVerticalRealization y) := by
  have h := canonicalNativeVerticalTraceBoundaryWedge_eq_verticalWronskian
    q x y
  unfold canonicalNativeVerticalTraceBoundaryWedge at h
  simpa [mixedScalarBoundaryWedge] using congrArg Neg.neg h

/-! ## The actual C3 edge cores already carried by the seeded ledger -/

/-- Ordinary C3 edge core at a cutoff and parameter. This is the
finitely-supported TFVD/G_pre state used by the existing ledger. -/
def canonicalCompletedC3OrdinaryEdgeCore
    (M : ℕ) (s : ℂ) : NativeGpreComplexEdgeCore :=
  (seededCompletedTfvdGreenLedger M s).1.1.2

/-- Logarithmic C3 edge core at a cutoff and parameter. -/
def canonicalCompletedC3LogJetEdgeCore
    (M : ℕ) (s : ℂ) : NativeGpreComplexEdgeCore :=
  (seededCompletedTfvdGreenLedger M s).1.2.2

/-- The ordinary core is constructed directly from the finite native
Dirichlet-gradient prefix, with no moment or kernel input. -/
theorem canonicalCompletedC3OrdinaryEdgeCore_eq_prefixCore
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3OrdinaryEdgeCore M s =
      c2DirichletGradientPrefixCore s (3 * M) := by
  rw [canonicalCompletedC3OrdinaryEdgeCore,
    seededCompletedTfvdGreenLedger_ordinary]
  rfl

/-- The logarithmic core is constructed directly from the finite native
log-jet prefix. -/
theorem canonicalCompletedC3LogJetEdgeCore_eq_prefixCore
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3LogJetEdgeCore M s =
      c2LogJetPrefixCore s (3 * M) := by
  rw [canonicalCompletedC3LogJetEdgeCore,
    seededCompletedTfvdGreenLedger_logJet]
  rfl

/-- The ordinary core's canonical vertical realization is literally the
ordinary C3 prefix state. -/
theorem canonicalCompletedC3OrdinaryEdgeCore_realization_eq_prefix
    (M : ℕ) (s : ℂ) :
    nativeGpreCanonicalVerticalRealization
        (canonicalCompletedC3OrdinaryEdgeCore M s) =
      canonicalCompletedC3DirichletGradientPrefixState s (3 * M) := by
  calc
    nativeGpreCanonicalVerticalRealization
        (canonicalCompletedC3OrdinaryEdgeCore M s) =
        (seededCompletedTfvdGreenLedger M s).1.1.1 := by
          exact (seededCompletedTfvdGreenLedger_ordinary_vertical_eq_provenance
            M s).symm
    _ = canonicalCompletedC3DirichletGradientPrefixState s (3 * M) :=
      seededCompletedTfvdGreenLedger_ordinary_vertical_eq_prefix M s

/-- The logarithmic core's canonical vertical realization is literally the
log-jet C3 prefix state. -/
theorem canonicalCompletedC3LogJetEdgeCore_realization_eq_prefix
    (M : ℕ) (s : ℂ) :
    nativeGpreCanonicalVerticalRealization
        (canonicalCompletedC3LogJetEdgeCore M s) =
      canonicalCompletedC3LogJetPrefixState s (3 * M) := by
  calc
    nativeGpreCanonicalVerticalRealization
        (canonicalCompletedC3LogJetEdgeCore M s) =
        (seededCompletedTfvdGreenLedger M s).1.2.1 := by
          exact (seededCompletedTfvdGreenLedger_logJet_vertical_eq_provenance
            M s).symm
    _ = canonicalCompletedC3LogJetPrefixState s (3 * M) :=
      seededCompletedTfvdGreenLedger_logJet_vertical_eq_prefix M s

/-- The ordinary native product edge state retains both the vertical prefix
and its original provenance core. -/
def canonicalCompletedC3OrdinaryEdgeState
    (M : ℕ) (s : ℂ) : NativeGpreTfvdProductState :=
  nativeGpreCanonicalTfvdGlue
    (canonicalCompletedC3OrdinaryEdgeCore M s)

/-- The log-jet native product edge state retains both the vertical prefix and
its original provenance core. -/
def canonicalCompletedC3LogJetEdgeState
    (M : ℕ) (s : ℂ) : NativeGpreTfvdProductState :=
  nativeGpreCanonicalTfvdGlue
    (canonicalCompletedC3LogJetEdgeCore M s)

@[simp] theorem canonicalCompletedC3OrdinaryEdgeState_apply
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3OrdinaryEdgeState M s =
      (canonicalCompletedC3DirichletGradientPrefixState s (3 * M),
        c2DirichletGradientPrefixCore s (3 * M)) := by
  rw [canonicalCompletedC3OrdinaryEdgeState,
    nativeGpreCanonicalTfvdGlue_apply,
    canonicalCompletedC3OrdinaryEdgeCore_realization_eq_prefix,
    canonicalCompletedC3OrdinaryEdgeCore_eq_prefixCore]

@[simp] theorem canonicalCompletedC3LogJetEdgeState_apply
    (M : ℕ) (s : ℂ) :
    canonicalCompletedC3LogJetEdgeState M s =
      (canonicalCompletedC3LogJetPrefixState s (3 * M),
        c2LogJetPrefixCore s (3 * M)) := by
  rw [canonicalCompletedC3LogJetEdgeState,
    nativeGpreCanonicalTfvdGlue_apply,
    canonicalCompletedC3LogJetEdgeCore_realization_eq_prefix,
    canonicalCompletedC3LogJetEdgeCore_eq_prefixCore]

/-- Applying the finite glued boundary pencil to these cores retains the
ordinary/log-jet provenance traces, and its Green defect is the vertical
Wronskian of the corresponding C3 prefixes. -/
theorem canonicalCompletedC3OrdinaryLogJetTraceGlue
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (M : ℕ) (z w : ℂ) :
    canonicalNativeFiniteGluedHilbertTraceGreenDefect q S
        (canonicalCompletedC3OrdinaryEdgeCore M w)
        (canonicalCompletedC3LogJetEdgeCore M z) =
      carryWeightedVerticalBoundaryWronskian q
        (canonicalCompletedC3DirichletGradientPrefixState w (3 * M))
        (canonicalCompletedC3LogJetPrefixState z (3 * M)) := by
  rw [canonicalNativeFiniteGluedHilbertTraceGreenDefect_eq_verticalWronskian,
    canonicalCompletedC3OrdinaryEdgeCore_realization_eq_prefix,
    canonicalCompletedC3LogJetEdgeCore_realization_eq_prefix]

/-- Explicit mismatch between the scalar C3 head wedge and the native glued
Hilbert trace defect for the corresponding ordinary/logarithmic edge cores.
This is a definition-level comparison: it does not assert that the mismatch
vanishes. -/
def canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (M : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
      (finiteBracketedDirichletChart 3 M z)
      (finiteCanonicalLogBracketChart M z)
      (finiteBracketedDirichletChart 3 M w)
      (finiteCanonicalLogBracketChart M w) -
    canonicalNativeFiniteGluedHilbertTraceGreenDefect q S
      (canonicalCompletedC3OrdinaryEdgeCore M w)
      (canonicalCompletedC3LogJetEdgeCore M z)

/-- The crosswalk defect is exactly the scalar C3 head wedge minus the
vertical Wronskian of the canonical finite ordinary/log edge states. -/
theorem canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect_eq_head_sub_verticalWronskian
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (M : ℕ) (z w : ℂ) :
    canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect q S M z w =
      mixedScalarBoundaryWedge
          (finiteBracketedDirichletChart 3 M z)
          (finiteCanonicalLogBracketChart M z)
          (finiteBracketedDirichletChart 3 M w)
          (finiteCanonicalLogBracketChart M w) -
        carryWeightedVerticalBoundaryWronskian q
          (canonicalCompletedC3DirichletGradientPrefixState w (3 * M))
          (canonicalCompletedC3LogJetPrefixState z (3 * M)) := by
  unfold canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect
  rw [canonicalCompletedC3OrdinaryLogJetTraceGlue]

/-- The exact algebraic decomposition of the C3-to-native crosswalk defect.
The first summand is the already named scalar C3 structural defect; the
second records the mismatch between the finite reflected C3 Green form and the
native vertical Wronskian of the canonical edge cores. -/
def canonicalCompletedC3FiniteReflectedGreenToNativeVerticalDefect
    (q : ℝ) (M : ℕ) (z w : ℂ) : ℂ :=
  greenForm (𝕜 := ℂ)
      (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
      (finiteC3GenuineBracketGreenBoundaryPair
        (3 * M) (reflectedParameter z)) -
    carryWeightedVerticalBoundaryWronskian q
      (canonicalCompletedC3DirichletGradientPrefixState w (3 * M))
      (canonicalCompletedC3LogJetPrefixState z (3 * M))

/-- The native trace crosswalk retains both independently defined residuals;
no cancellation is asserted. -/
theorem canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect_eq_structural_add_nativeGreenMismatch
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (M : ℕ) (z w : ℂ) :
    canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect q S M z w =
      canonicalC3FiniteMixedStructuralDefect M z w +
        canonicalCompletedC3FiniteReflectedGreenToNativeVerticalDefect q M z w := by
  unfold canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect
    canonicalCompletedC3FiniteReflectedGreenToNativeVerticalDefect
  have h := canonicalC3FiniteMixedHeadWronskian_eq_green_add_structuralDefect
    M z w
  rw [canonicalCompletedC3OrdinaryLogJetTraceGlue]
  rw [h]
  ring

/-! ## What the current APIs do and do not identify -/

/-- The existing C3 structural defect remains the exact difference between
the scalar C3 mixed head wedge and its finite reflected Green form. The
native trace-glue theorem does not silently set this scalar residual to zero. -/
theorem canonicalC3FiniteMixedStructuralDefect_eq_headScalarizationResidual
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedStructuralDefect M z w =
      mixedScalarBoundaryWedge
          (finiteBracketedDirichletChart 3 M z)
          (finiteCanonicalLogBracketChart M z)
          (finiteBracketedDirichletChart 3 M w)
          (finiteCanonicalLogBracketChart M w) -
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter z)) := by
  have h := canonicalC3FiniteMixedHeadWronskian_eq_green_add_structuralDefect
    M z w
  rw [h]
  ring

/-- The full native Hilbert trace-glue is exact for every finite atlas and
every edge-core pair. This is the load-bearing cancellation statement for
the native carrier. -/
theorem canonicalNativeFiniteHilbertTraceGlue_is_exact :
    ∀ (q : ℝ) (S : Finset NativeGpreBoundaryContext)
      (x y : NativeGpreComplexEdgeCore),
      canonicalNativeFiniteGluedHilbertTraceGreenDefect q S x y =
        carryWeightedVerticalBoundaryWronskian q
          (nativeGpreCanonicalVerticalRealization x)
          (nativeGpreCanonicalVerticalRealization y) :=
  fun q S x y =>
    canonicalNativeFiniteGluedHilbertTraceGreenDefect_eq_verticalWronskian
      q S x y

/-- The same cancellation for the full vertical Hilbert space. -/
theorem canonicalNativeHilbertTraceGlue_is_exact :
    ∀ (q : ℝ) (S : Finset NativeGpreBoundaryContext)
      (x y : CarryVerticalL2),
      canonicalNativeHilbertGluedTraceGreenDefect q S x y =
        carryWeightedVerticalBoundaryWronskian q x y :=
  fun q S x y =>
    canonicalNativeHilbertGluedTraceGreenDefect_eq_verticalWronskian q S x y

end

end CarrySelfAdjointOperator

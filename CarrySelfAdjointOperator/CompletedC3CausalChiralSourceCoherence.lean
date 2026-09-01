import CarrySelfAdjointOperator.CompletedC3CausalChiralBoundaryRelation
import Mathlib.Tactic

/-!
# Coherence of the completed C3 causal chiral source

The enriched chiral source carrier deliberately stores the ambient Gamma
response twice: once in its explicitly typed Gamma coordinate and once as the
direct Naimark coordinate of the completed all-cutoff state.  These two
coordinates are independent on the unrestricted ambient direct sum, which is
why a `direct-only` vector obstructs a global chiral factorization.

For every canonical completed source the two coordinates agree exactly.  This
module packages their difference as a bounded real-linear coherence defect,
proves that the entire causal source span lies in its kernel, and replaces the
ambient chiral readout by an equivalent readout using the stored all-cutoff
coordinate on that coherent subspace.

No boundary sewing, moment positivity, characteristic zero, or spectral
hypothesis is used.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## The duplicated direct coordinate -/

/-- The type-only Gamma view bundled as an additive map.  The source and
target use the same two real Naimark quadratures; only the scalar-space
instance changes. -/
def canonicalCompletedC3GammaNaimarkViewAddHom :
    RealifiedNaimarkComplexification →+ CarryGammaComplexNaimark where
  toFun := canonicalCompletedC3GammaNaimarkView
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The additive type-only view is continuous because both carriers have the
same `L2` topology.  Real linearity then follows canonically from continuity. -/
def canonicalCompletedC3GammaNaimarkViewContinuousLinearMap :
    RealifiedNaimarkComplexification →L[ℝ] CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkViewAddHom.toRealLinearMap (by
    change Continuous (fun u : RealifiedNaimarkComplexification => u)
    exact continuous_id)

@[simp] theorem canonicalCompletedC3GammaNaimarkView_zero :
    canonicalCompletedC3GammaNaimarkView
        (0 : RealifiedNaimarkComplexification) = 0 :=
  canonicalCompletedC3GammaNaimarkViewContinuousLinearMap.map_zero

/-- Direct Naimark coordinate retained inside the completed all-cutoff state,
viewed in the canonical complex Gamma carrier. -/
def canonicalCompletedC3OnePointStoredDirectReadout :
    CanonicalCompletedC3AllCutoffOnePointHilbert →L[ℝ]
      CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkViewContinuousLinearMap.comp
    (WithLp.fstL 2 ℝ
      RealifiedNaimarkComplexification
      (WithLp 2
        (RealifiedNaimarkComplexification ×
          WithLp 2
            (RealifiedNaimarkComplexification ×
              CanonicalCompletedC3AllCutoffOnePointTraceHilbert))))

@[simp] theorem canonicalCompletedC3OnePointStoredDirectReadout_apply
    (state : CanonicalCompletedC3AllCutoffOnePointHilbert) :
    canonicalCompletedC3OnePointStoredDirectReadout state =
      canonicalCompletedC3GammaNaimarkView state.direct := by
  simp [canonicalCompletedC3OnePointStoredDirectReadout,
    canonicalCompletedC3GammaNaimarkViewContinuousLinearMap,
    canonicalCompletedC3GammaNaimarkViewAddHom,
    CanonicalCompletedC3AllCutoffOnePointHilbert.direct]

/-- The same stored direct coordinate, read from the common enriched source. -/
def canonicalCompletedC3EnrichedStoredDirectReadout :
    CanonicalCompletedC3EnrichedChiralSourceCarrier →L[ℝ]
      CarryGammaComplexNaimark :=
  canonicalCompletedC3OnePointStoredDirectReadout.comp
    ((WithLp.fstL 2 ℝ
        CanonicalCompletedC3AllCutoffOnePointHilbert
        CanonicalCompletedC3ArchimedeanChartOperatorCarrier).comp
      (WithLp.sndL 2 ℝ
        CarryGammaComplexNaimark
        (WithLp 2
          (CanonicalCompletedC3AllCutoffOnePointHilbert ×
            CanonicalCompletedC3ArchimedeanChartOperatorCarrier))))

@[simp] theorem canonicalCompletedC3EnrichedStoredDirectReadout_apply
    (state : CanonicalCompletedC3EnrichedChiralSourceCarrier) :
    canonicalCompletedC3EnrichedStoredDirectReadout state =
      canonicalCompletedC3GammaNaimarkView state.snd.fst.direct := by
  simp [canonicalCompletedC3EnrichedStoredDirectReadout]

/-- The newly bundled readout is exactly the Gamma view of the realified
direct readout already used by the coisometric camera construction. -/
theorem canonicalCompletedC3EnrichedStoredDirectReadout_eq_gammaView_realified
    (state : CanonicalCompletedC3EnrichedChiralSourceCarrier) :
    canonicalCompletedC3EnrichedStoredDirectReadout state =
      canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3EnrichedRealifiedDirectReadout state) := by
  rw [canonicalCompletedC3EnrichedStoredDirectReadout_apply]
  rfl

/-- Bounded vector defect between the explicitly typed Gamma response and the
same response retained inside the completed all-cutoff state. -/
def canonicalCompletedC3EnrichedDirectCoherenceDefect :
    CanonicalCompletedC3EnrichedChiralSourceCarrier →L[ℝ]
      CarryGammaComplexNaimark :=
  canonicalCompletedC3EnrichedDirectNaimarkReadout -
    canonicalCompletedC3EnrichedStoredDirectReadout

@[simp] theorem canonicalCompletedC3EnrichedDirectCoherenceDefect_apply
    (state : CanonicalCompletedC3EnrichedChiralSourceCarrier) :
    canonicalCompletedC3EnrichedDirectCoherenceDefect state =
      canonicalCompletedC3EnrichedDirectNaimarkReadout state -
        canonicalCompletedC3EnrichedStoredDirectReadout state :=
  rfl

/-- The canonical completed source has no duplicated-coordinate defect. -/
@[simp] theorem canonicalCompletedC3EnrichedDirectCoherenceDefect_sourceState
    (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedDirectCoherenceDefect
        (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) = 0 := by
  rw [canonicalCompletedC3EnrichedDirectCoherenceDefect_apply,
    canonicalCompletedC3EnrichedDirectNaimarkReadout_sourceState_eq_view,
    canonicalCompletedC3EnrichedStoredDirectReadout_apply]
  exact sub_self _

/-! ## The coherent physical subspace -/

/-- Closed linear subspace on which the two retained ambient-response
coordinates agree. -/
def canonicalCompletedC3EnrichedDirectCoherentSubmodule :
    Submodule ℝ CanonicalCompletedC3EnrichedChiralSourceCarrier :=
  canonicalCompletedC3EnrichedDirectCoherenceDefect.ker

theorem canonicalCompletedC3EnrichedChiralSourceState_mem_directCoherent
    (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedChiralSourceState z hzStrip ∈
      canonicalCompletedC3EnrichedDirectCoherentSubmodule := by
  change canonicalCompletedC3EnrichedDirectCoherenceDefect
      (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) = 0
  exact canonicalCompletedC3EnrichedDirectCoherenceDefect_sourceState
    z hzStrip

/-- Every real-linear combination of canonical completed sources retains the
same exact direct-coordinate coherence. -/
theorem canonicalCompletedC3CausalChiralSourceSubmodule_le_directCoherent :
    canonicalCompletedC3CausalChiralSourceSubmodule ≤
      canonicalCompletedC3EnrichedDirectCoherentSubmodule := by
  rw [canonicalCompletedC3CausalChiralSourceSubmodule, Submodule.span_le]
  intro state hstate
  rcases hstate with ⟨z, hzStrip, rfl⟩
  exact canonicalCompletedC3EnrichedChiralSourceState_mem_directCoherent
    z hzStrip

/-- On the coherent subspace the explicitly typed Gamma response is recovered
exactly from the direct coordinate already stored in the all-cutoff state. -/
theorem canonicalCompletedC3EnrichedDirectNaimarkReadout_eq_stored_of_mem
    {state : CanonicalCompletedC3EnrichedChiralSourceCarrier}
    (hstate : state ∈ canonicalCompletedC3EnrichedDirectCoherentSubmodule) :
    canonicalCompletedC3EnrichedDirectNaimarkReadout state =
      canonicalCompletedC3EnrichedStoredDirectReadout state := by
  change canonicalCompletedC3EnrichedDirectCoherenceDefect state = 0 at hstate
  rw [canonicalCompletedC3EnrichedDirectCoherenceDefect_apply,
    sub_eq_zero] at hstate
  exact hstate

/-- Membership in the closed coherence subspace is the existing pointwise
Naimark-coherence predicate, now expressed as a linear kernel. -/
theorem canonicalCompletedC3EnrichedDirectCoherentSubmodule_mem_iff
    (state : CanonicalCompletedC3EnrichedChiralSourceCarrier) :
    state ∈ canonicalCompletedC3EnrichedDirectCoherentSubmodule ↔
      CanonicalCompletedC3NaimarkCoherentSource state := by
  change canonicalCompletedC3EnrichedDirectCoherenceDefect state = 0 ↔
    canonicalCompletedC3EnrichedDirectNaimarkReadout state =
      canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3EnrichedRealifiedDirectReadout state)
  rw [canonicalCompletedC3EnrichedDirectCoherenceDefect_apply,
    sub_eq_zero,
    canonicalCompletedC3EnrichedStoredDirectReadout_eq_gammaView_realified]

/-! ## Elimination of the ambient `direct-only` obstruction -/

@[simp] theorem canonicalCompletedC3EnrichedStoredDirectReadout_directOnly
    (u : CarryGammaComplexNaimark) :
    canonicalCompletedC3EnrichedStoredDirectReadout
        (canonicalCompletedC3EnrichedDirectOnlySource u) = 0 := by
  simp [canonicalCompletedC3EnrichedStoredDirectReadout,
    canonicalCompletedC3EnrichedDirectOnlySource,
    CanonicalCompletedC3AllCutoffOnePointHilbert.direct]

@[simp] theorem canonicalCompletedC3EnrichedDirectCoherenceDefect_directOnly
    (u : CarryGammaComplexNaimark) :
    canonicalCompletedC3EnrichedDirectCoherenceDefect
        (canonicalCompletedC3EnrichedDirectOnlySource u) = u := by
  rw [canonicalCompletedC3EnrichedDirectCoherenceDefect_apply,
    canonicalCompletedC3EnrichedDirectNaimarkReadout_directOnly,
    canonicalCompletedC3EnrichedStoredDirectReadout_directOnly]
  exact sub_zero u

/-- A pure external Gamma coordinate is physically coherent only when it is
zero.  Thus the witness refuting ambient factorization is absent from the
coherent source space. -/
theorem canonicalCompletedC3EnrichedDirectOnlySource_mem_directCoherent_iff
    (u : CarryGammaComplexNaimark) :
    canonicalCompletedC3EnrichedDirectOnlySource u ∈
        canonicalCompletedC3EnrichedDirectCoherentSubmodule ↔
      u = 0 := by
  change canonicalCompletedC3EnrichedDirectCoherenceDefect
      (canonicalCompletedC3EnrichedDirectOnlySource u) = 0 ↔ u = 0
  rw [canonicalCompletedC3EnrichedDirectCoherenceDefect_directOnly]

theorem canonicalCompletedC3EnrichedDirectOnlySource_not_mem_causal
    (u : CarryGammaComplexNaimark) (hu : u ≠ 0) :
    canonicalCompletedC3EnrichedDirectOnlySource u ∉
      canonicalCompletedC3CausalChiralSourceSubmodule := by
  intro hcausal
  have hcoherent :=
    canonicalCompletedC3CausalChiralSourceSubmodule_le_directCoherent hcausal
  exact hu
    ((canonicalCompletedC3EnrichedDirectOnlySource_mem_directCoherent_iff u).1
      hcoherent)

/-- Exact Naimark coherence still permits a promoted camera response with no
scalar trace.  The next restriction in route B must therefore be the causal
response-to-trace graph, not merely equality of the duplicated coordinates. -/
theorem canonicalCompletedC3EnrichedCoherentPortOnlySource_mem_directCoherent
    (u : RealifiedCameraComplexification) :
    canonicalCompletedC3EnrichedCoherentPortOnlySource u ∈
      canonicalCompletedC3EnrichedDirectCoherentSubmodule := by
  rw [canonicalCompletedC3EnrichedDirectCoherentSubmodule_mem_iff]
  exact canonicalCompletedC3EnrichedCoherentPortOnlySource_naimarkCoherent u

/-- Consequently even the closed direct-coherence subspace is too large for
a global factorization through the positive Wronskian trace. -/
theorem no_directCoherent_positive_to_coisometricCameraChiral_factorization
    (z : ℂ) (hzIm : 0 < z.im)
    (u : RealifiedCameraComplexification) (hu : u ≠ 0) :
    ¬ ∃ T :
        CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℝ]
          CanonicalCompletedC3CoisometricCameraChiralEnergyCarrier,
      ∀ state : CanonicalCompletedC3EnrichedChiralSourceCarrier,
        state ∈ canonicalCompletedC3EnrichedDirectCoherentSubmodule →
          canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state =
            T (canonicalCompletedC3EnrichedPositiveChiralReadout z state) := by
  rintro ⟨T, hfactor⟩
  exact
    (no_naimarkCoherent_positive_to_coisometricCameraChiral_factorization
      z hzIm u hu)
      ⟨T, fun state hcoherent =>
        hfactor state
          ((canonicalCompletedC3EnrichedDirectCoherentSubmodule_mem_iff
            state).2 hcoherent)⟩

/-! ## Coherent replacement of the enlarged chiral readout -/

/-- Scaled ambient readout reconstructed from the direct coordinate retained
inside the completed all-cutoff state. -/
def canonicalCompletedC3EnrichedStoredScaledAmbientReadout
    (z : ℂ) :
    CanonicalCompletedC3EnrichedChiralSourceCarrier →L[ℝ]
      CarryGammaComplexNaimark :=
  (canonicalCompletedC3RealifiedComplexScale
      (((Real.sqrt (2 * z.im) : ℝ) : ℂ))).comp
    canonicalCompletedC3EnrichedStoredDirectReadout

/-- Enlarged chiral readout with no independent external-response coordinate.
It uses the stored all-cutoff response together with the unchanged negative
Wronskian chirality. -/
def canonicalCompletedC3EnrichedDirectCoherentChiralReadout
    (z : ℂ) :
    CanonicalCompletedC3EnrichedChiralSourceCarrier →L[ℝ]
      CanonicalCompletedC3CoisometricChiralEnergyCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ
      CarryGammaComplexNaimark
      CanonicalCompletedC3FullWronskianOperatorCarrier).symm
    |>.toContinuousLinearMap.comp
      ((canonicalCompletedC3EnrichedStoredScaledAmbientReadout z).prod
        (canonicalCompletedC3EnrichedNegativeChiralReadout z))

/-- On every coherent source, the reconstructed enlarged readout is exactly
the original one. -/
theorem canonicalCompletedC3EnrichedDirectCoherentChiralReadout_eq_of_mem
    (z : ℂ) {state : CanonicalCompletedC3EnrichedChiralSourceCarrier}
    (hstate : state ∈ canonicalCompletedC3EnrichedDirectCoherentSubmodule) :
    canonicalCompletedC3EnrichedDirectCoherentChiralReadout z state =
      canonicalCompletedC3EnrichedCoisometricChiralReadout z state := by
  have hdirect :=
    canonicalCompletedC3EnrichedDirectNaimarkReadout_eq_stored_of_mem hstate
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (((Real.sqrt (2 * z.im) : ℝ) : ℂ) •
        canonicalCompletedC3EnrichedStoredDirectReadout state) =
      (((Real.sqrt (2 * z.im) : ℝ) : ℂ) •
        canonicalCompletedC3EnrichedDirectNaimarkReadout state)
    rw [hdirect]
  · rfl

/-- In particular, the reconstructed coherent readout gives the same concrete
coisometric/chiral state on every canonical completed source. -/
theorem canonicalCompletedC3EnrichedDirectCoherentChiralReadout_sourceState
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedDirectCoherentChiralReadout z
        (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) =
      canonicalCompletedC3CoisometricChiralEnergyState M z hzStrip.1 := by
  rw [canonicalCompletedC3EnrichedDirectCoherentChiralReadout_eq_of_mem z
      (canonicalCompletedC3EnrichedChiralSourceState_mem_directCoherent
        z hzStrip)]
  exact canonicalCompletedC3EnrichedCoisometricChiralReadout_sourceState
    M z hzStrip

end

end CarrySelfAdjointOperator

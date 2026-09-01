import CarrySelfAdjointOperator.CompletedC3EnrichedChiralReadoutTransformation
import CarrySelfAdjointOperator.CompletedC3NaimarkCoisometricBlock
import Mathlib.Tactic

/-!
# Coisometric camera/chiral transformation

The completed ambient response is not an arbitrary Naimark vector: its
realified coordinate is the Naimark promotion of the completed symplectic
camera state.  Therefore the canonical coisometric readout recovers that
camera state exactly.  This module combines that camera readout with the
negative full-Wronskian chirality and proves that the resulting block has the
same energy as the ambient coisometric/chiral block.

The final section audits the strength of this substitution.  Compatibility
of the two typed Naimark coordinates alone is not enough to factor the block
through the positive Wronskian readout: a coherent promoted-camera direction
can still carry zero scalar trace.  Thus the remaining restriction must also
encode the causal response-to-trace relation.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Camera-space form of the coisometric/chiral energy block. -/
abbrev CanonicalCompletedC3CoisometricCameraChiralEnergyCarrier :=
  WithLp 2
    (RealifiedCameraComplexification ×
      CanonicalCompletedC3FullWronskianOperatorCarrier)

/-- The canonical camera response paired with the retained negative
Wronskian chirality. -/
def canonicalCompletedC3CoisometricCameraChiralEnergyState
    (M : ℕ) (z : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    CanonicalCompletedC3CoisometricCameraChiralEnergyCarrier :=
  WithLp.toLp 2
    (Real.sqrt (2 * z.im) •
        completedC3SymplecticCameraState
          (operatorHeightParameter z) hzHalf,
      canonicalCompletedC3FullWronskianNegativePolarization
        (canonicalCompletedC3NormalizedFullWronskianOperatorState M z))

/-- Realified direct coordinate retained inside the completed one-point
state of the enriched source. -/
def canonicalCompletedC3EnrichedRealifiedDirectReadout :
    CanonicalCompletedC3EnrichedChiralSourceCarrier →L[ℝ]
      RealifiedNaimarkComplexification :=
  (WithLp.fstL 2 ℝ
      RealifiedNaimarkComplexification
      (WithLp 2
        (RealifiedNaimarkComplexification ×
          WithLp 2
            (RealifiedNaimarkComplexification ×
              CanonicalCompletedC3AllCutoffOnePointTraceHilbert)))).comp
    ((WithLp.fstL 2 ℝ
        CanonicalCompletedC3AllCutoffOnePointHilbert
        CanonicalCompletedC3ArchimedeanChartOperatorCarrier).comp
      (WithLp.sndL 2 ℝ
        CarryGammaComplexNaimark
        (WithLp 2
          (CanonicalCompletedC3AllCutoffOnePointHilbert ×
            CanonicalCompletedC3ArchimedeanChartOperatorCarrier))))

/-- Canonical coisometric camera compression of the retained direct
Naimark coordinate. -/
def canonicalCompletedC3EnrichedCameraReadout :
    CanonicalCompletedC3EnrichedChiralSourceCarrier →L[ℝ]
      RealifiedCameraComplexification :=
  realifiedNaimarkAdjoint.comp
    canonicalCompletedC3EnrichedRealifiedDirectReadout

/-- Real scalar multiplication bundled as a continuous real-linear map. -/
def canonicalCompletedC3RealScale
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a : ℝ) : H →L[ℝ] H :=
  a • ContinuousLinearMap.id ℝ H

@[simp] theorem canonicalCompletedC3RealScale_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a : ℝ) (x : H) :
    canonicalCompletedC3RealScale a x = a • x :=
  rfl

/-- Coisometric camera/chiral readout from the common enriched source. -/
def canonicalCompletedC3EnrichedCoisometricCameraChiralReadout
    (z : ℂ) :
    CanonicalCompletedC3EnrichedChiralSourceCarrier →L[ℝ]
      CanonicalCompletedC3CoisometricCameraChiralEnergyCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ
      RealifiedCameraComplexification
      CanonicalCompletedC3FullWronskianOperatorCarrier).symm
    |>.toContinuousLinearMap.comp
      (((canonicalCompletedC3RealScale (Real.sqrt (2 * z.im))).comp
          canonicalCompletedC3EnrichedCameraReadout).prod
        (canonicalCompletedC3EnrichedNegativeChiralReadout z))

/-! ## Exact action on the canonical completed source -/

@[simp] theorem canonicalCompletedC3EnrichedRealifiedDirectReadout_sourceState
    (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedRealifiedDirectReadout
        (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) =
      completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hzStrip.1 :=
  rfl

theorem canonicalCompletedC3EnrichedCameraReadout_sourceState
    (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedCameraReadout
        (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) =
      completedC3SymplecticCameraState
        (operatorHeightParameter z) hzStrip.1 := by
  rw [canonicalCompletedC3EnrichedCameraReadout,
    ContinuousLinearMap.comp_apply,
    canonicalCompletedC3EnrichedRealifiedDirectReadout_sourceState]
  unfold completedC3SymplecticNaimarkState
  change (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort)
      (completedC3SymplecticCameraState
        (operatorHeightParameter z) hzStrip.1) = _
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

/-- The coisometric substitution produces exactly the concrete camera/chiral
state on the canonical completed source. -/
theorem canonicalCompletedC3EnrichedCoisometricCameraChiralReadout_sourceState
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z
        (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) =
      canonicalCompletedC3CoisometricCameraChiralEnergyState
        M z hzStrip.1 := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change Real.sqrt (2 * z.im) •
        canonicalCompletedC3EnrichedCameraReadout
          (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) = _
    rw [canonicalCompletedC3EnrichedCameraReadout_sourceState]
    rfl
  · exact canonicalCompletedC3EnrichedNegativeChiralReadout_sourceState
      M z hzStrip

/-! ## Exact energy preservation -/

/-- The typed ambient response has exactly the norm of its intrinsic camera
preimage. -/
theorem norm_canonicalCompletedC3AmbientResponseState_eq_camera
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ =
      ‖completedC3SymplecticCameraState
        (operatorHeightParameter z) hzHalf‖ := by
  unfold canonicalCompletedC3AmbientResponseState
    completedC3SymplecticNaimarkState
    canonicalCompletedC3GammaNaimarkView
  exact norm_realifiedNaimarkPort _

/-- Pythagoras for the camera/chiral form of the block. -/
theorem norm_sq_canonicalCompletedC3CoisometricCameraChiralEnergyState
    (M : ℕ) (z : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hzIm : 0 ≤ z.im) :
    ‖canonicalCompletedC3CoisometricCameraChiralEnergyState
        M z hzHalf‖ ^ 2 =
      2 * z.im *
          ‖completedC3SymplecticCameraState
            (operatorHeightParameter z) hzHalf‖ ^ 2 +
        ‖canonicalCompletedC3FullWronskianNegativePolarization
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 := by
  unfold canonicalCompletedC3CoisometricCameraChiralEnergyState
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change
    ‖Real.sqrt (2 * z.im) •
        completedC3SymplecticCameraState
          (operatorHeightParameter z) hzHalf‖ ^ 2 + _ = _
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have htwoIm : 0 ≤ 2 * z.im := by positivity
  change
    (Real.sqrt (2 * z.im) *
        ‖completedC3SymplecticCameraState
          (operatorHeightParameter z) hzHalf‖) ^ 2 +
        ‖canonicalCompletedC3FullWronskianNegativePolarization
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 = _
  rw [mul_pow, Real.sq_sqrt htwoIm]

/-- The camera substitution preserves the complete coisometric/chiral
energy on every canonical state. -/
theorem norm_sq_coisometricCameraChiral_eq_coisometricChiral
    (M : ℕ) (z : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hzIm : 0 ≤ z.im) :
    ‖canonicalCompletedC3CoisometricCameraChiralEnergyState
        M z hzHalf‖ ^ 2 =
      ‖canonicalCompletedC3CoisometricChiralEnergyState
        M z hzHalf‖ ^ 2 := by
  rw [norm_sq_canonicalCompletedC3CoisometricCameraChiralEnergyState
      M z hzHalf hzIm,
    norm_sq_canonicalCompletedC3CoisometricChiralEnergyState
      M z hzHalf hzIm,
    norm_canonicalCompletedC3AmbientResponseState_eq_camera]

/-! ## Naimark coherence alone is not causal trace coherence -/

/-- Compatibility of the explicitly typed ambient coordinate with the
realified direct coordinate retained in the one-point state. -/
def CanonicalCompletedC3NaimarkCoherentSource
    (state : CanonicalCompletedC3EnrichedChiralSourceCarrier) : Prop :=
  canonicalCompletedC3EnrichedDirectNaimarkReadout state =
    canonicalCompletedC3GammaNaimarkView
      (canonicalCompletedC3EnrichedRealifiedDirectReadout state)

theorem canonicalCompletedC3EnrichedChiralSourceState_naimarkCoherent
    (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    CanonicalCompletedC3NaimarkCoherentSource
      (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) :=
  rfl

/-- A promoted camera direction with all reflected, trace, and chart
coordinates zero. -/
def canonicalCompletedC3EnrichedCoherentPortOnlySource
    (u : RealifiedCameraComplexification) :
    CanonicalCompletedC3EnrichedChiralSourceCarrier :=
  WithLp.toLp 2
    (canonicalCompletedC3GammaNaimarkView (realifiedNaimarkPort u),
      WithLp.toLp 2
        (WithLp.toLp 2 (realifiedNaimarkPort u, 0), 0))

@[simp] theorem canonicalCompletedC3EnrichedCoherentPortOnlySource_naimarkCoherent
    (u : RealifiedCameraComplexification) :
    CanonicalCompletedC3NaimarkCoherentSource
      (canonicalCompletedC3EnrichedCoherentPortOnlySource u) :=
  rfl

@[simp] theorem canonicalCompletedC3EnrichedTraceReadout_coherentPortOnly
    (u : RealifiedCameraComplexification) :
    canonicalCompletedC3EnrichedTraceReadout
        (canonicalCompletedC3EnrichedCoherentPortOnlySource u) = 0 := by
  unfold canonicalCompletedC3EnrichedTraceReadout
    canonicalCompletedC3EnrichedCoherentPortOnlySource
  simp [CanonicalCompletedC3AllCutoffOnePointHilbert.completedCompanion,
    CanonicalCompletedC3AllCutoffOnePointHilbert.completedValue,
    CanonicalCompletedC3AllCutoffOnePointHilbert.valueHead,
    CanonicalCompletedC3AllCutoffOnePointHilbert.logJetHead,
    CanonicalCompletedC3AllCutoffOnePointHilbert.valueTail,
    CanonicalCompletedC3AllCutoffOnePointHilbert.logJetTail]

@[simp] theorem canonicalCompletedC3EnrichedArchimedeanReadout_coherentPortOnly
    (u : RealifiedCameraComplexification) :
    canonicalCompletedC3EnrichedArchimedeanReadout
        (canonicalCompletedC3EnrichedCoherentPortOnlySource u) = 0 :=
  rfl

@[simp] theorem canonicalCompletedC3EnrichedNormalizedFullWronskianReadout_coherentPortOnly
    (z : ℂ) (u : RealifiedCameraComplexification) :
    canonicalCompletedC3EnrichedNormalizedFullWronskianReadout z
        (canonicalCompletedC3EnrichedCoherentPortOnlySource u) = 0 := by
  unfold canonicalCompletedC3EnrichedNormalizedFullWronskianReadout
    canonicalCompletedC3RealifiedComplexScale
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    canonicalCompletedC3EnrichedTraceReadout_coherentPortOnly,
    canonicalCompletedC3EnrichedArchimedeanReadout_coherentPortOnly, map_zero]
  exact map_zero _

@[simp] theorem canonicalCompletedC3EnrichedPositiveChiralReadout_coherentPortOnly
    (z : ℂ) (u : RealifiedCameraComplexification) :
    canonicalCompletedC3EnrichedPositiveChiralReadout z
        (canonicalCompletedC3EnrichedCoherentPortOnlySource u) = 0 := by
  rw [canonicalCompletedC3EnrichedPositiveChiralReadout,
    ContinuousLinearMap.comp_apply,
    canonicalCompletedC3EnrichedNormalizedFullWronskianReadout_coherentPortOnly,
    map_zero]

@[simp] theorem canonicalCompletedC3EnrichedCameraReadout_coherentPortOnly
    (u : RealifiedCameraComplexification) :
    canonicalCompletedC3EnrichedCameraReadout
        (canonicalCompletedC3EnrichedCoherentPortOnlySource u) = u := by
  unfold canonicalCompletedC3EnrichedCameraReadout
    canonicalCompletedC3EnrichedRealifiedDirectReadout
    canonicalCompletedC3EnrichedCoherentPortOnlySource
  change (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort) u = u
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

theorem canonicalCompletedC3EnrichedCoisometricCameraChiralReadout_coherentPortOnly_ne_zero
    (z : ℂ) (hzIm : 0 < z.im)
    (u : RealifiedCameraComplexification) (hu : u ≠ 0) :
    canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z
        (canonicalCompletedC3EnrichedCoherentPortOnlySource u) ≠ 0 := by
  intro hzero
  have hfst := congrArg WithLp.fst hzero
  unfold canonicalCompletedC3EnrichedCoisometricCameraChiralReadout at hfst
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,
    canonicalCompletedC3RealScale_apply,
    canonicalCompletedC3EnrichedCameraReadout_coherentPortOnly] at hfst
  change Real.sqrt (2 * z.im) • u = 0 at hfst
  have hsqrt : Real.sqrt (2 * z.im) ≠ 0 := by
    positivity
  exact (smul_ne_zero hsqrt hu) hfst

/-- Even after imposing exact Naimark coherence, no global linear map can
factor the coisometric camera/chiral block through the positive Wronskian
readout.  The missing restriction is specifically the causal relation between
the Green response and its completed value/log-jet traces. -/
theorem no_naimarkCoherent_positive_to_coisometricCameraChiral_factorization
    (z : ℂ) (hzIm : 0 < z.im)
    (u : RealifiedCameraComplexification) (hu : u ≠ 0) :
    ¬ ∃ T :
        CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℝ]
          CanonicalCompletedC3CoisometricCameraChiralEnergyCarrier,
      ∀ state : CanonicalCompletedC3EnrichedChiralSourceCarrier,
        CanonicalCompletedC3NaimarkCoherentSource state →
          canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state =
            T (canonicalCompletedC3EnrichedPositiveChiralReadout z state) := by
  rintro ⟨T, hfactor⟩
  have happ := hfactor
    (canonicalCompletedC3EnrichedCoherentPortOnlySource u)
    (canonicalCompletedC3EnrichedCoherentPortOnlySource_naimarkCoherent u)
  rw [canonicalCompletedC3EnrichedPositiveChiralReadout_coherentPortOnly,
    map_zero] at happ
  exact
    (canonicalCompletedC3EnrichedCoisometricCameraChiralReadout_coherentPortOnly_ne_zero
      z hzIm u hu) happ

end

end CarrySelfAdjointOperator

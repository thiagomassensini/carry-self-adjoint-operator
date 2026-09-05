import C3ProjectiveCompletedJetBridge
import FiniteEnrichedCameraState
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# C3 projective Hilbert realization and the exact R/B total crosswalk

The projective TFVD carrier has the product topology, so it should not be
silently assigned an ambient Hilbert norm.  Its closed image nevertheless has
a canonical Hilbert geometry: pull the `CarryVerticalL2` inner product through
the injective projective analysis and its continuous left inverse.

Finite real-plane camera states are then obtained by reconstructing the common
vertical state and restricting its coordinates.  At every finite level the
canonical visible/blind analysis reconstructs this state exactly.  Restricting
after reconstruction or reconstructing after restriction gives the same total
state, even though the visible and blind summands need not agree separately.

The final theorem records the complementary obstruction.  The raw undressing
maps `x |-> q^(-n) x_n` cannot have a cutoff-uniform bound on all of `l²` when
`0 < q < 1`.  Hence the uniform Hilbert port must retain the native dressing
or use a correspondingly weighted target norm.
-/

open scoped BigOperators Topology lp ENNReal NNReal Matrix

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- The canonical Hilbert model of the closed projective image.  The type is
the native vertical Hilbert space itself; the map below realizes it faithfully
inside the simultaneous projective TFVD data. -/
abbrev NativeGpreTfvdProjectiveHilbert := CarryVerticalL2

/-- Faithful realization of the canonical Hilbert model in all finite TFVD
and provenance atlases simultaneously. -/
def nativeGpreTfvdProjectiveHilbertRealization (q : ℝ) :
    NativeGpreTfvdProjectiveHilbert →L[ℂ]
      NativeGpreTfvdProjectiveAnalysisCarrier :=
  nativeGpreTfvdProjectiveAnalysis q

/-- Continuous recovery of the Hilbert representative from projective data. -/
def nativeGpreTfvdProjectiveHilbertRecovery
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    NativeGpreTfvdProjectiveAnalysisCarrier →L[ℂ]
      NativeGpreTfvdProjectiveHilbert :=
  nativeGpreTfvdProjectiveReconstruction q hq0 hq1

/-- Exact round trip: the Hilbert realization loses no state. -/
theorem nativeGpreTfvdProjectiveHilbertRecovery_realization
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    nativeGpreTfvdProjectiveHilbertRecovery q hqpos.le hq1 ∘L
        nativeGpreTfvdProjectiveHilbertRealization q =
      ContinuousLinearMap.id ℂ NativeGpreTfvdProjectiveHilbert := by
  apply ContinuousLinearMap.ext
  intro x
  exact nativeGpreTfvdProjectiveReconstruction_analysis q hqpos hq1 x

/-- Inner product transported from the recovered native state.  It is the
canonical Hilbert form on the projective image (and only a semidefinite form
away from that image). -/
def nativeGpreTfvdProjectivePulledBackInner
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (data₁ data₂ : NativeGpreTfvdProjectiveAnalysisCarrier) : ℂ :=
  inner ℂ
    (nativeGpreTfvdProjectiveHilbertRecovery q hq0 hq1 data₁)
    (nativeGpreTfvdProjectiveHilbertRecovery q hq0 hq1 data₂)

/-- On realized data, the pulled-back form is literally the original Hilbert
inner product. -/
theorem nativeGpreTfvdProjectivePulledBackInner_realization
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x y : NativeGpreTfvdProjectiveHilbert) :
    nativeGpreTfvdProjectivePulledBackInner q hqpos.le hq1
        (nativeGpreTfvdProjectiveHilbertRealization q x)
        (nativeGpreTfvdProjectiveHilbertRealization q y) =
      inner ℂ x y := by
  rw [nativeGpreTfvdProjectivePulledBackInner,
    nativeGpreTfvdProjectiveHilbertRecovery,
    nativeGpreTfvdProjectiveHilbertRealization,
    nativeGpreTfvdProjectiveReconstruction_analysis q hqpos hq1,
    nativeGpreTfvdProjectiveReconstruction_analysis q hqpos hq1]

/-- Every finite atlas is a bounded camera port out of the same Hilbert
carrier. -/
def nativeGpreTfvdFiniteHilbertPort
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    NativeGpreTfvdProjectiveHilbert →L[ℂ]
      NativeGpreFiniteTfvdAnalysisCarrier S :=
  nativeGpreFiniteTfvdAnalysis q S

/-- The finite Hilbert ports commute exactly with atlas restriction. -/
theorem nativeGpreTfvdFiniteHilbertPort_restrict
    (q : ℝ) {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T) :
    nativeGpreFiniteTfvdAnalysisRestriction hST ∘L
        nativeGpreTfvdFiniteHilbertPort q T =
      nativeGpreTfvdFiniteHilbertPort q S := by
  apply ContinuousLinearMap.ext
  intro x
  exact nativeGpreFiniteTfvdAnalysis_restrict q hST x

/-- Every finite Hilbert port has the exact TFVD left inverse. -/
theorem nativeGpreFiniteTfvdReconstruction_comp_finiteHilbertPort
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S ∘L
        nativeGpreTfvdFiniteHilbertPort q S =
      ContinuousLinearMap.id ℂ NativeGpreTfvdProjectiveHilbert :=
  nativeGpreFiniteTfvdReconstruction_comp_analysis q hqpos hq1 S

/-- Finite real coordinate state recovered from arbitrary projective data. -/
def nativeGpreProjectiveFiniteRealState
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) : Fin N → ℝ :=
  fun n ↦
    (nativeGpreTfvdProjectiveHilbertRecovery q hq0 hq1 data n.1).re

/-- Finite imaginary coordinate state recovered from the same projective
datum; together the two functions retain the native real plane. -/
def nativeGpreProjectiveFiniteImagState
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) : Fin N → ℝ :=
  fun n ↦
    (nativeGpreTfvdProjectiveHilbertRecovery q hq0 hq1 data n.1).im

/-- Real coordinates of realized projective data are exactly those of the
original Hilbert state. -/
theorem nativeGpreProjectiveFiniteRealState_realization
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (N : ℕ)
    (x : NativeGpreTfvdProjectiveHilbert) :
    nativeGpreProjectiveFiniteRealState q hqpos.le hq1 N
        (nativeGpreTfvdProjectiveHilbertRealization q x) =
      fun n : Fin N ↦ (x n.1).re := by
  funext n
  rw [nativeGpreProjectiveFiniteRealState,
    nativeGpreTfvdProjectiveHilbertRecovery,
    nativeGpreTfvdProjectiveHilbertRealization,
    nativeGpreTfvdProjectiveReconstruction_analysis q hqpos hq1]

/-- The same exact recovery for the second real coordinate. -/
theorem nativeGpreProjectiveFiniteImagState_realization
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (N : ℕ)
    (x : NativeGpreTfvdProjectiveHilbert) :
    nativeGpreProjectiveFiniteImagState q hqpos.le hq1 N
        (nativeGpreTfvdProjectiveHilbertRealization q x) =
      fun n : Fin N ↦ (x n.1).im := by
  funext n
  rw [nativeGpreProjectiveFiniteImagState,
    nativeGpreTfvdProjectiveHilbertRecovery,
    nativeGpreTfvdProjectiveHilbertRealization,
    nativeGpreTfvdProjectiveReconstruction_analysis q hqpos hq1]

/-! ## The cutoff-uniform undressing obstruction -/

/-- On the normalized coordinate vector, undressing has exact size `q^(-n)`. -/
theorem norm_carryWeightedUndressedEval_single
    (q : ℝ) (hqpos : 0 < q) (n : ℕ) :
  ‖carryWeightedUndressedEval q n
        (lp.single 2 n (1 : ℂ) : CarryVerticalL2)‖ =
      (q⁻¹) ^ n := by
  rw [carryWeightedUndressedEval_apply]
  simp only [lp.coeFn_single, Pi.single_eq_same, mul_one, norm_inv,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
  rw [inv_pow]

/-- There is no cutoff-independent bound for all raw undressed coordinate
ports on the ambient native `l²` space. -/
theorem not_exists_uniform_carryWeightedUndressedEval_bound
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, ∀ x : CarryVerticalL2,
      ‖carryWeightedUndressedEval q n x‖ ≤ C * ‖x‖ := by
  rintro ⟨C, hC⟩
  have hqinv : 1 < q⁻¹ := (one_lt_inv₀ hqpos).2 hq1
  have hdiv : Tendsto (fun n : ℕ ↦ (q⁻¹) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hqinv
  have heventually : ∀ᶠ n : ℕ in atTop, C < (q⁻¹) ^ n :=
    hdiv.eventually_gt_atTop C
  rcases heventually.exists with ⟨n, hn⟩
  have hbound := hC n (lp.single 2 n (1 : ℂ) : CarryVerticalL2)
  rw [norm_carryWeightedUndressedEval_single q hqpos n,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one,
    mul_one] at hbound
  exact (not_lt_of_ge hbound) hn

/-- The correctly redressed all-depth port is the native Hilbert identity.
The parameter is retained in the name because the coordinate theorem below
shows that it is precisely `q^n` times the undressed port. -/
def carryWeightedRedressedAllDepthPort (_q : ℝ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  ContinuousLinearMap.id ℂ CarryVerticalL2

@[simp] theorem carryWeightedRedressedAllDepthPort_apply
    (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedRedressedAllDepthPort q x = x := rfl

/-- Coordinatewise, restoring the native weight after undressing cancels
exactly. -/
theorem carryWeightedRedressedAllDepthPort_coordinate
    (q : ℝ) (hq : q ≠ 0) (x : CarryVerticalL2) (n : ℕ) :
    carryWeightedRedressedAllDepthPort q x n =
      (q : ℂ) ^ n * carryWeightedUndressedEval q n x := by
  rw [carryWeightedRedressedAllDepthPort_apply,
    carryWeightedUndressedEval_apply]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  simp [pow_ne_zero n hqC]

/-- Consequently the redressed simultaneous camera port has exact norm one
on every state. -/
theorem norm_carryWeightedRedressedAllDepthPort
    (q : ℝ) (x : CarryVerticalL2) :
    ‖carryWeightedRedressedAllDepthPort q x‖ = ‖x‖ := by
  rw [carryWeightedRedressedAllDepthPort_apply]

end

end CPFormal.Analytic.Cp

namespace NativeCarryC3Crosswalk

noncomputable section

/-! ## Exact finite R/B reconstruction and total cutoff intertwining -/

variable {camera state : Type*}
  [Fintype camera] [DecidableEq camera]
  [Fintype state] [DecidableEq state]

/-- Vector form of the enriched Parseval reconstruction. -/
theorem finiteCanonicalEnrichedCamera_reconstruct_vector
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef)
    (x : state → ℝ) :
    (finiteCanonicalCameraReadout C)ᵀ *ᵥ
          (finiteCanonicalCameraReadout C *ᵥ x) +
        (finiteCanonicalCameraBlindProjection C)ᵀ *ᵥ
          (finiteCanonicalCameraBlindProjection C *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
    finiteCanonicalEnrichedCamera_parseval hG, Matrix.one_mulVec]

/-- Total visible-plus-blind synthesis at one finite camera level. -/
def finiteCanonicalEnrichedCameraTotal
    (C : Matrix camera state ℝ) (x : state → ℝ) : state → ℝ :=
  (finiteCanonicalCameraReadout C)ᵀ *ᵥ
      (finiteCanonicalCameraReadout C *ᵥ x) +
    (finiteCanonicalCameraBlindProjection C)ᵀ *ᵥ
      (finiteCanonicalCameraBlindProjection C *ᵥ x)

@[simp] theorem finiteCanonicalEnrichedCameraTotal_eq
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) (x : state → ℝ) :
    finiteCanonicalEnrichedCameraTotal C x = x :=
  finiteCanonicalEnrichedCamera_reconstruct_vector hG x

/-- Restriction of a finite state along an inclusion of coordinate labels. -/
def finiteStateRestriction {small large : Type*}
    (embedding : small ↪ large) (x : large → ℝ) : small → ℝ :=
  fun i ↦ x (embedding i)

/-- The *total* enriched R/B reconstruction commutes with every finite state
restriction.  No compatibility of the visible and blind summands separately
is assumed. -/
theorem finiteCanonicalEnrichedCamera_total_restrict
    {smallCamera largeCamera smallState largeState : Type*}
    [Fintype smallCamera] [DecidableEq smallCamera]
    [Fintype largeCamera] [DecidableEq largeCamera]
    [Fintype smallState] [DecidableEq smallState]
    [Fintype largeState] [DecidableEq largeState]
    {Csmall : Matrix smallCamera smallState ℝ}
    {Clarge : Matrix largeCamera largeState ℝ}
    (hGsmall : (finiteCameraRowGram Csmall).PosDef)
    (hGlarge : (finiteCameraRowGram Clarge).PosDef)
    (embedding : smallState ↪ largeState)
    (x : largeState → ℝ) :
    finiteStateRestriction embedding
        ((finiteCanonicalCameraReadout Clarge)ᵀ *ᵥ
            (finiteCanonicalCameraReadout Clarge *ᵥ x) +
          (finiteCanonicalCameraBlindProjection Clarge)ᵀ *ᵥ
            (finiteCanonicalCameraBlindProjection Clarge *ᵥ x)) =
      (finiteCanonicalCameraReadout Csmall)ᵀ *ᵥ
          (finiteCanonicalCameraReadout Csmall *ᵥ
            finiteStateRestriction embedding x) +
        (finiteCanonicalCameraBlindProjection Csmall)ᵀ *ᵥ
          (finiteCanonicalCameraBlindProjection Csmall *ᵥ
            finiteStateRestriction embedding x) := by
  rw [finiteCanonicalEnrichedCamera_reconstruct_vector hGlarge,
    finiteCanonicalEnrichedCamera_reconstruct_vector hGsmall]

open CPFormal.Analytic.Cp

/-- The real coordinate of every finite projective state is reconstructed
exactly by its canonical visible/blind camera pair. -/
theorem nativeGpreProjectiveFiniteRealState_rb_reconstruct
    {finiteCamera : Type*} [Fintype finiteCamera]
    [DecidableEq finiteCamera]
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    {C : Matrix finiteCamera (Fin N) ℝ}
    (hG : (finiteCameraRowGram C).PosDef)
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) :
    (finiteCanonicalCameraReadout C)ᵀ *ᵥ
          (finiteCanonicalCameraReadout C *ᵥ
            nativeGpreProjectiveFiniteRealState q hq0 hq1 N data) +
        (finiteCanonicalCameraBlindProjection C)ᵀ *ᵥ
          (finiteCanonicalCameraBlindProjection C *ᵥ
            nativeGpreProjectiveFiniteRealState q hq0 hq1 N data) =
      nativeGpreProjectiveFiniteRealState q hq0 hq1 N data :=
  finiteCanonicalEnrichedCamera_reconstruct_vector hG _

/-- The same exact R/B reconstruction for the second coordinate of the native
real plane. -/
theorem nativeGpreProjectiveFiniteImagState_rb_reconstruct
    {finiteCamera : Type*} [Fintype finiteCamera]
    [DecidableEq finiteCamera]
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    {C : Matrix finiteCamera (Fin N) ℝ}
    (hG : (finiteCameraRowGram C).PosDef)
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) :
    (finiteCanonicalCameraReadout C)ᵀ *ᵥ
          (finiteCanonicalCameraReadout C *ᵥ
            nativeGpreProjectiveFiniteImagState q hq0 hq1 N data) +
        (finiteCanonicalCameraBlindProjection C)ᵀ *ᵥ
          (finiteCanonicalCameraBlindProjection C *ᵥ
            nativeGpreProjectiveFiniteImagState q hq0 hq1 N data) =
      nativeGpreProjectiveFiniteImagState q hq0 hq1 N data :=
  finiteCanonicalEnrichedCamera_reconstruct_vector hG _

/-- Canonical inclusion of a shorter coordinate prefix into a longer one. -/
def finitePrefixEmbedding {N K : ℕ} (hNK : N ≤ K) : Fin N ↪ Fin K where
  toFun n := ⟨n.1, lt_of_lt_of_le n.2 hNK⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun z : Fin K ↦ z.1) hij

/-- The finite real states recovered from projective data commute exactly with
prefix restriction. -/
theorem nativeGpreProjectiveFiniteRealState_restrict
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    {N K : ℕ} (hNK : N ≤ K)
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) :
    finiteStateRestriction (finitePrefixEmbedding hNK)
        (nativeGpreProjectiveFiniteRealState q hq0 hq1 K data) =
      nativeGpreProjectiveFiniteRealState q hq0 hq1 N data := by
  funext n
  rfl

/-- The same prefix compatibility for the second real-plane coordinate. -/
theorem nativeGpreProjectiveFiniteImagState_restrict
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    {N K : ℕ} (hNK : N ≤ K)
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) :
    finiteStateRestriction (finitePrefixEmbedding hNK)
        (nativeGpreProjectiveFiniteImagState q hq0 hq1 K data) =
      nativeGpreProjectiveFiniteImagState q hq0 hq1 N data := by
  funext n
  rfl

/-- Direct C3/RB cutoff crosswalk for the first real-plane coordinate: the
large-cutoff total R/B state restricts to the small-cutoff total R/B state. -/
theorem nativeGpreProjectiveFiniteRealState_rb_total_cutoff_intertwines
    {smallCamera largeCamera : Type*}
    [Fintype smallCamera] [DecidableEq smallCamera]
    [Fintype largeCamera] [DecidableEq largeCamera]
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    {N K : ℕ} (hNK : N ≤ K)
    {Csmall : Matrix smallCamera (Fin N) ℝ}
    {Clarge : Matrix largeCamera (Fin K) ℝ}
    (hGsmall : (finiteCameraRowGram Csmall).PosDef)
    (hGlarge : (finiteCameraRowGram Clarge).PosDef)
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) :
    finiteStateRestriction (finitePrefixEmbedding hNK)
        (finiteCanonicalEnrichedCameraTotal Clarge
          (nativeGpreProjectiveFiniteRealState q hq0 hq1 K data)) =
      finiteCanonicalEnrichedCameraTotal Csmall
        (nativeGpreProjectiveFiniteRealState q hq0 hq1 N data) := by
  rw [finiteCanonicalEnrichedCameraTotal_eq hGlarge,
    finiteCanonicalEnrichedCameraTotal_eq hGsmall,
    nativeGpreProjectiveFiniteRealState_restrict q hq0 hq1 hNK data]

/-- The same direct cutoff crosswalk for the second real-plane coordinate. -/
theorem nativeGpreProjectiveFiniteImagState_rb_total_cutoff_intertwines
    {smallCamera largeCamera : Type*}
    [Fintype smallCamera] [DecidableEq smallCamera]
    [Fintype largeCamera] [DecidableEq largeCamera]
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    {N K : ℕ} (hNK : N ≤ K)
    {Csmall : Matrix smallCamera (Fin N) ℝ}
    {Clarge : Matrix largeCamera (Fin K) ℝ}
    (hGsmall : (finiteCameraRowGram Csmall).PosDef)
    (hGlarge : (finiteCameraRowGram Clarge).PosDef)
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) :
    finiteStateRestriction (finitePrefixEmbedding hNK)
        (finiteCanonicalEnrichedCameraTotal Clarge
          (nativeGpreProjectiveFiniteImagState q hq0 hq1 K data)) =
      finiteCanonicalEnrichedCameraTotal Csmall
        (nativeGpreProjectiveFiniteImagState q hq0 hq1 N data) := by
  rw [finiteCanonicalEnrichedCameraTotal_eq hGlarge,
    finiteCanonicalEnrichedCameraTotal_eq hGsmall,
    nativeGpreProjectiveFiniteImagState_restrict q hq0 hq1 hNK data]

end


end NativeCarryC3Crosswalk

#print axioms CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveHilbertRecovery_realization
#print axioms CPFormal.Analytic.Cp.nativeGpreTfvdProjectivePulledBackInner_realization
#print axioms CPFormal.Analytic.Cp.nativeGpreTfvdFiniteHilbertPort_restrict
#print axioms CPFormal.Analytic.Cp.not_exists_uniform_carryWeightedUndressedEval_bound
#print axioms CPFormal.Analytic.Cp.carryWeightedRedressedAllDepthPort_coordinate
#print axioms NativeCarryC3Crosswalk.finiteCanonicalEnrichedCamera_total_restrict
#print axioms NativeCarryC3Crosswalk.nativeGpreProjectiveFiniteRealState_rb_reconstruct
#print axioms NativeCarryC3Crosswalk.nativeGpreProjectiveFiniteRealState_restrict
#print axioms NativeCarryC3Crosswalk.nativeGpreProjectiveFiniteRealState_rb_total_cutoff_intertwines

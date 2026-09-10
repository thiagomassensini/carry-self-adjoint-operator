import CarrySelfAdjointOperator.MultibaseTfvdCameraGramHilbertTransport
import CarrySelfAdjointOperator.CanonicalC3GlobalCameraBoundaryBridge
import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import CarrySelfAdjointOperator.CenteredCameraCutoffConvergence
import NativeCarrySpectralWeyl.Infinite.CameraCompletion
import NativeCarrySpectralWeyl.Infinite.Naimark
import Mathlib.Tactic

/-!
# Enriched moving-camera / completed Naimark crosswalk

This module records the part of the moving-camera construction that is
already canonical in the repository.

A finite camera matrix acts only on the outer camera index of a family of
vertical TFVD states.  The visible component is the canonical whitened
readout and the blind component is the complementary projection.  The
Hilbert-valued lift inherits the exact Parseval and raw-Gram identities from
the finite matrix construction.

The completed Naimark roundtrip is recorded for the concrete completed C3
state.  The finite moving pair and the all-cutoff completed TFVD/Naimark
state are intentionally kept as different carriers.  No theorem in this
module identifies a cutoff-dependent blind projection with the projective
Gpre provenance carrier.
-/

open scoped BigOperators Matrix lp

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite
open CPFormal.Analytic.Cp

namespace CarrySelfAdjointOperator

noncomputable section

/-- A finite enriched moving-camera state.  Its first component is the
camera-visible family and its second component is the full state-indexed
blind/provenance family.  The two indices remain external camera/state
indices; the values are unchanged CarryVerticalL2 vectors. -/
def finiteEnrichedMovingCameraTfvdState
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X : FiniteHilbertFamily state CarryVerticalL2) :
    FiniteHilbertFamily camera CarryVerticalL2 ×
      FiniteHilbertFamily state CarryVerticalL2 :=
  (finiteCanonicalCameraHilbertReadout C X,
    finiteHilbertMatrixSynthesis
      (finiteCanonicalCameraBlindProjection C) X)

@[simp] theorem finiteEnrichedMovingCameraTfvdState_visible
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X : FiniteHilbertFamily state CarryVerticalL2) :
    (finiteEnrichedMovingCameraTfvdState C X).1 =
      finiteCanonicalCameraHilbertReadout C X :=
  rfl

@[simp] theorem finiteEnrichedMovingCameraTfvdState_blind
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X : FiniteHilbertFamily state CarryVerticalL2) :
    (finiteEnrichedMovingCameraTfvdState C X).2 =
      finiteHilbertMatrixSynthesis
        (finiteCanonicalCameraBlindProjection C) X :=
  rfl

/-- The visible and blind parts of the moving state retain the complete
pairing.  This is Parseval before taking any cutoff or completion limit. -/
theorem finiteEnrichedMovingCameraTfvdState_parseval
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X Y : FiniteHilbertFamily state CarryVerticalL2) :
    inner ℂ (finiteEnrichedMovingCameraTfvdState C X).1
        (finiteEnrichedMovingCameraTfvdState C Y).1 +
      inner ℂ (finiteEnrichedMovingCameraTfvdState C X).2
        (finiteEnrichedMovingCameraTfvdState C Y).2 =
      inner ℂ X Y := by
  simpa [finiteEnrichedMovingCameraTfvdState] using
    (finiteCanonicalEnrichedCameraHilbert_parseval
      (C := C) hG X Y)

/-- The visible synthesis and blind complement reconstruct the full
state-valued TFVD family exactly.  This is the vector form of the finite
enrichment, before any limit is considered. -/
theorem finiteEnrichedMovingCameraTfvdState_reconstruct
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X : FiniteHilbertFamily state CarryVerticalL2) :
    finiteCanonicalCameraHilbertSynthesis C
        (finiteEnrichedMovingCameraTfvdState C X).1 +
      (finiteEnrichedMovingCameraTfvdState C X).2 = X := by
  change finiteHilbertMatrixSynthesis (finiteCanonicalCameraSynthesis C)
      (finiteHilbertMatrixSynthesis (finiteCanonicalCameraReadout C) X) +
      finiteHilbertMatrixSynthesis
        (finiteCanonicalCameraBlindProjection C) X = X
  rw [finiteHilbertMatrixSynthesis_comp]
  apply PiLp.ext
  intro j
  change
    (∑ k : state, ((finiteCanonicalCameraProjection C j k : ℝ) : ℂ) •
        X.ofLp k) +
      (∑ k : state,
        ((finiteCanonicalCameraBlindProjection C j k : ℝ) : ℂ) •
          X.ofLp k) =
      X.ofLp j
  rw [← Finset.sum_add_distrib]
  calc
    Finset.univ.sum (fun x : state =>
        ((finiteCanonicalCameraProjection C j x : ℝ) : ℂ) • X.ofLp x +
          ((finiteCanonicalCameraBlindProjection C j x : ℝ) : ℂ) •
            X.ofLp x) =
        Finset.univ.sum (fun x : state =>
          (if j = x then (1 : ℂ) else 0) • X.ofLp x) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hPB :
          finiteCanonicalCameraProjection C +
              finiteCanonicalCameraBlindProjection C =
            (1 : Matrix state state ℝ) := by
        ext i l
        simp [finiteCanonicalCameraBlindProjection]
      have hentry := congr_fun (congr_fun hPB j) k
      rw [← add_smul]
      congr 1
      by_cases hjk : j = k
      · simp [Matrix.one_apply, hjk] at hentry ⊢
        exact_mod_cast hentry
      · simp [hjk] at hentry ⊢
        exact_mod_cast hentry
    _ = X.ofLp j := by
      classical
      calc
        (∑ x : state, (if j = x then (1 : ℂ) else 0) • X.ofLp x) =
            ∑ x : state, if j = x then X.ofLp x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          split_ifs <;> simp
        _ = X.ofLp j := by
          rw [Finset.sum_ite_eq]
          simp

/-- The raw literal camera synthesis induces exactly the row-Gram pairing on
vertical TFVD-valued channels. -/
theorem finiteEnrichedMovingCameraTfvdState_raw_gram
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera]
    (C : Matrix camera state ℝ)
    (X Y : FiniteHilbertFamily camera CarryVerticalL2) :
    inner ℂ
        (finiteCameraHilbertRawSynthesis C X)
        (finiteCameraHilbertRawSynthesis C Y) =
      ∑ i : camera, ∑ j : camera,
        (((finiteCameraRowGram C i j : ℝ) : ℂ) *
          inner ℂ (X.ofLp i) (Y.ofLp j)) :=
  finiteCameraHilbertRawSynthesis_inner C X Y

/-- A single outer-channel test exposes an off-diagonal row-Gram entry
without identifying that entry with a vertical TFVD coordinate. -/
theorem finiteEnrichedMovingCameraTfvdState_raw_single_channel
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera]
    (C : Matrix camera state ℝ) (i j : camera)
    (x y : CarryVerticalL2) :
    inner ℂ
        (finiteCameraHilbertRawSynthesis C
          (finiteHilbertCoordinate i x))
        (finiteCameraHilbertRawSynthesis C
          (finiteHilbertCoordinate j y)) =
      (((finiteCameraRowGram C i j : ℝ) : ℂ) * inner ℂ x y) :=
  finiteCameraHilbertRawSynthesis_single_channel C i j x y

/-- The canonical whitened synthesis is isometric on the outer camera
family.  This is the Hilbert-valued lift of V^T V = I. -/
theorem finiteEnrichedMovingCameraTfvdState_whitened_synthesis_isometry
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X Y : FiniteHilbertFamily camera CarryVerticalL2) :
    inner ℂ
        (finiteCanonicalCameraHilbertSynthesis C X)
        (finiteCanonicalCameraHilbertSynthesis C Y) =
      inner ℂ X Y :=
  finiteCanonicalCameraHilbertSynthesis_isometry C hG X Y

/-- The canonical whitened readout is a left inverse of the whitened
synthesis on camera-valued TFVD families. -/
theorem finiteEnrichedMovingCameraTfvdState_whitened_roundtrip
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X : FiniteHilbertFamily camera CarryVerticalL2) :
    finiteCanonicalCameraHilbertReadout C
        (finiteCanonicalCameraHilbertSynthesis C X) = X :=
  finiteCanonicalCameraHilbertReadout_synthesis C hG X

/-- The finite enriched moving state is exactly the pair of its visible
whitened readout and its blind/provenance complement. -/
theorem finiteEnrichedMovingCameraTfvdState_pairing
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X Y : FiniteHilbertFamily state CarryVerticalL2) :
    inner ℂ (finiteEnrichedMovingCameraTfvdState C X).1
        (finiteEnrichedMovingCameraTfvdState C Y).1 +
      inner ℂ (finiteEnrichedMovingCameraTfvdState C X).2
        (finiteEnrichedMovingCameraTfvdState C Y).2 =
      inner ℂ X Y :=
  finiteEnrichedMovingCameraTfvdState_parseval C hG X Y

/-- Internal vertical linear maps commute with every external camera matrix
lift.  In particular, an existing TFVD map may be applied before or after
the finite camera whitening/lift. -/
theorem finiteEnrichedMovingCameraTfvdState_internal_map_commutes
    {input output K : Type*}
    [Fintype input] [Fintype output]
    [NormedAddCommGroup K] [Module ℂ K]
    (A : Matrix output input ℝ)
    (T : CarryVerticalL2 →ₗ[ℂ] K)
    (X : FiniteHilbertFamily input CarryVerticalL2) :
    finiteHilbertMatrixSynthesis A
        (WithLp.toLp (2 : ENNReal) (fun i => T (X.ofLp i))) =
      WithLp.toLp (2 : ENNReal)
        (fun j => T ((finiteHilbertMatrixSynthesis A X).ofLp j)) :=
  finiteHilbertMatrixSynthesis_map_linearMap_commutes A T X

/-- The concrete completed C3 Naimark state has an exact coordinate-free
camera roundtrip.  This is a vector equality in the existing realified
Naimark/camera carriers. -/
theorem canonicalCompletedC3NaimarkState_camera_roundtrip (z : ℂ) :
    realifiedNaimarkAdjoint (canonicalCompletedC3NaimarkState z) =
      canonicalCompletedC3SixCameraSource z :=
  realifiedNaimarkAdjoint_canonicalCompletedC3NaimarkState z

/-- Equivalent roundtrip phrased through the canonical state readout map. -/
theorem canonicalCompletedC3State_camera_readout_roundtrip (z : ℂ) :
    canonicalCameraStateReadout
        c3SixCameraNaimarkRealization
        (canonicalCompletedOperatorC3State z) =
      canonicalCompletedC3SixCameraSource z :=
  canonicalCompletedC3GlobalCameraReadout_eq_source z

/-- The all-cutoff completed TFVD/Genuine Naimark vectors already converge in
one fixed global carrier.  This theorem is intentionally separate from the
finite cutoff-dependent whitening above. -/
theorem canonicalCompletedTfvdGreenAllCutoffNaimarkState_fixed_carrier_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun M : ℕ => canonicalCompletedTfvdGreenAllCutoffNaimarkState M s)
      Filter.atTop
      (nhds (completedC3SymplecticNaimarkState s hs)) :=
  canonicalCompletedTfvdGreenAllCutoffNaimarkState_tendsto hs

/-- The Naimark roundtrip is coherent for any state realization that is
already in the range of the canonical port. -/
theorem canonicalCameraStateReadout_coherent_roundtrip
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (q : H →L[ℝ] RealifiedCameraComplexification) :
    canonicalCameraStateReadout
        (realifiedNaimarkPort ∘L q) = q :=
  canonicalCameraStateReadout_of_coherent q

end

end CarrySelfAdjointOperator

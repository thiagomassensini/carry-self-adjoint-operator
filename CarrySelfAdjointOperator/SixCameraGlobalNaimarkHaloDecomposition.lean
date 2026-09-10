import CarrySelfAdjointOperator.SixCameraCenteredLogNaimarkVarianceCrosswalk
import CarrySelfAdjointOperator.CompletedC3NaimarkCoisometricBlock
import Mathlib.Tactic

/-!
# Six-camera global Naimark halo decomposition

This module works in the intrinsic real `NaimarkSpace`.  It identifies the
whitened six-camera synthesis with the restriction of the global
`CameraHilbert` Naimark realization, packages the global ordinary projector
and its escape, and proves the exact orthogonal decomposition of the
six-camera escape into a coherent all-camera halo and the global escape.

No equality with the raw BR2 state, no cutoff limit, and no identification
with Gpre or other provenance sectors is asserted here.
-/


open scoped BigOperators ENNReal MeasureTheory RealInnerProductSpace Matrix MatrixOrder
open Set MeasureTheory Filter intervalIntegral

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera

noncomputable section
set_option autoImplicit false

def sixCameraWhitenedCameraHilbertEmbedding (c : Fin 6 → ℝ) : CameraHilbert :=
  atlasSixCameraHilbertEmbedding (positiveInverseSqrt sixCameraGram *ᵥ c)

theorem naimarkIsometry_sixCameraWhitenedCameraHilbertEmbedding (c : Fin 6 → ℝ) :
    naimarkIsometry (sixCameraWhitenedCameraHilbertEmbedding c) =
      sixCameraWhitenedNaimarkSynthesis c := by
  simp [sixCameraWhitenedCameraHilbertEmbedding,
    atlasSixCameraHilbertEmbedding,
    sixCameraWhitenedNaimarkSynthesis,
    sixCameraNaimarkSynthesis,
    atlasSixCameraIndex]

theorem centeredCameraIsometry_sixCameraWhitenedCameraHilbertEmbedding (c : Fin 6 → ℝ) :
    centeredCameraIsometry (sixCameraWhitenedCameraHilbertEmbedding c) =
      sixCameraWhitenedCenteredLogNaimarkSynthesis c := by
  simp only [sixCameraWhitenedCameraHilbertEmbedding,
    atlasSixCameraHilbertEmbedding,
    map_sum, map_smul,
    sixCameraWhitenedCenteredLogNaimarkSynthesis,
    sixCameraCenteredLogNaimarkSynthesis]
  congr 1
  funext i
  rw [centeredCameraIsometry_cameraVector]

def globalNaimarkCameraProjection :
    NaimarkSpace →L[ℝ] NaimarkSpace :=
  naimarkIsometry.toContinuousLinearMap ∘L naimarkAdjoint

def globalNaimarkCameraEscape :
    NaimarkSpace →L[ℝ] NaimarkSpace :=
  (1 : NaimarkSpace →L[ℝ] NaimarkSpace) -
    globalNaimarkCameraProjection

@[simp] theorem globalNaimarkCameraProjection_apply (x : NaimarkSpace) :
    globalNaimarkCameraProjection x =
      naimarkIsometry (naimarkAdjoint x) := rfl

@[simp] theorem globalNaimarkCameraEscape_apply (x : NaimarkSpace) :
    globalNaimarkCameraEscape x =
      x - globalNaimarkCameraProjection x := rfl

theorem globalNaimarkCameraProjection_idempotent :
    globalNaimarkCameraProjection ∘L globalNaimarkCameraProjection =
      globalNaimarkCameraProjection := by
  apply ContinuousLinearMap.ext
  intro x
  change naimarkIsometry (naimarkAdjoint
    (naimarkIsometry (naimarkAdjoint x))) =
      naimarkIsometry (naimarkAdjoint x)
  have hleft : naimarkAdjoint
      (naimarkIsometry (naimarkAdjoint x)) = naimarkAdjoint x := by
    change (naimarkAdjoint ∘L naimarkIsometry.toContinuousLinearMap)
        (naimarkAdjoint x) = naimarkAdjoint x
    rw [naimarkAdjoint_comp_naimarkIsometry]
    rfl
  rw [hleft]

theorem globalNaimarkCameraProjection_idempotent_apply (x : NaimarkSpace) :
    globalNaimarkCameraProjection (globalNaimarkCameraProjection x) =
      globalNaimarkCameraProjection x := by
  exact congrArg (fun T : NaimarkSpace →L[ℝ] NaimarkSpace => T x)
    globalNaimarkCameraProjection_idempotent

theorem globalNaimarkCameraProjection_range :
    LinearMap.range globalNaimarkCameraProjection.toLinearMap =
      LinearMap.range naimarkIsometry.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨naimarkAdjoint x, rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨naimarkIsometry c, ?_⟩
    change globalNaimarkCameraProjection (naimarkIsometry c) =
      naimarkIsometry c
    change naimarkIsometry (naimarkAdjoint (naimarkIsometry c)) =
      naimarkIsometry c
    have h : naimarkAdjoint (naimarkIsometry c) = c := by
      change (naimarkAdjoint ∘L naimarkIsometry.toContinuousLinearMap) c = c
      rw [naimarkAdjoint_comp_naimarkIsometry]
      rfl
    rw [h]

theorem globalNaimarkCameraProjection_isSymmetric :
    globalNaimarkCameraProjection.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (naimarkIsometry (naimarkAdjoint x)) y =
    inner ℝ x (naimarkIsometry (naimarkAdjoint y))
  have hxy :
      inner ℝ (naimarkIsometry (naimarkAdjoint x)) y =
        inner ℝ (naimarkAdjoint x) (naimarkAdjoint y) := by
    simpa [naimarkAdjoint] using
      (naimarkIsometry.toContinuousLinearMap.adjoint_inner_right
        (naimarkAdjoint x) y).symm
  have hyx :
      inner ℝ (naimarkAdjoint y) (naimarkAdjoint x) =
        inner ℝ (naimarkIsometry (naimarkAdjoint y)) x := by
    simpa [naimarkAdjoint] using
      naimarkIsometry.toContinuousLinearMap.adjoint_inner_right
        (naimarkAdjoint y) x
  rw [hxy, ← real_inner_comm, hyx, real_inner_comm]

theorem globalNaimarkCameraProjection_inner_symm
    (x y : NaimarkSpace) :
    inner ℝ (globalNaimarkCameraProjection x) y =
      inner ℝ x (globalNaimarkCameraProjection y) := by
  have h := globalNaimarkCameraProjection_isSymmetric x y
  change inner ℝ (globalNaimarkCameraProjection x) y =
    inner ℝ x (globalNaimarkCameraProjection y) at h
  exact h

theorem globalNaimarkCameraProjection_isStarProjection :
    IsStarProjection globalNaimarkCameraProjection := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  refine ⟨?_, globalNaimarkCameraProjection_isSymmetric⟩
  change globalNaimarkCameraProjection.toLinearMap ∘ₗ
      globalNaimarkCameraProjection.toLinearMap =
    globalNaimarkCameraProjection.toLinearMap
  apply LinearMap.ext
  intro x
  change globalNaimarkCameraProjection (globalNaimarkCameraProjection x) =
    globalNaimarkCameraProjection x
  exact congrArg (fun T : NaimarkSpace →L[ℝ] NaimarkSpace => T x)
    globalNaimarkCameraProjection_idempotent

theorem globalNaimarkCameraProjection_fixes_sixCamera
    (c : Fin 6 → ℝ) :
    globalNaimarkCameraProjection
        (sixCameraWhitenedNaimarkSynthesis c) =
      sixCameraWhitenedNaimarkSynthesis c := by
  rw [← naimarkIsometry_sixCameraWhitenedCameraHilbertEmbedding]
  change naimarkIsometry
    (naimarkAdjoint
      (naimarkIsometry (sixCameraWhitenedCameraHilbertEmbedding c))) =
      naimarkIsometry (sixCameraWhitenedCameraHilbertEmbedding c)
  have hleft :
      naimarkAdjoint
        (naimarkIsometry (sixCameraWhitenedCameraHilbertEmbedding c)) =
        sixCameraWhitenedCameraHilbertEmbedding c := by
    change (naimarkAdjoint ∘L naimarkIsometry.toContinuousLinearMap)
        (sixCameraWhitenedCameraHilbertEmbedding c) =
      sixCameraWhitenedCameraHilbertEmbedding c
    rw [naimarkAdjoint_comp_naimarkIsometry]
    rfl
  rw [hleft]

theorem globalNaimarkCameraProjection_fixes_sixCameraProjection (x : NaimarkSpace) :
    globalNaimarkCameraProjection
        (sixCameraWhitenedNaimarkProjection x) =
      sixCameraWhitenedNaimarkProjection x := by
  rw [sixCameraWhitenedNaimarkProjection]
  rw [globalNaimarkCameraProjection_fixes_sixCamera]

theorem sixCameraProjection_globalNaimarkProjection (x : NaimarkSpace) :
    sixCameraWhitenedNaimarkProjection
        (globalNaimarkCameraProjection x) =
      sixCameraWhitenedNaimarkProjection x := by
  rw [sixCameraWhitenedNaimarkProjection, sixCameraWhitenedNaimarkProjection]
  congr 1
  funext i
  change inner ℝ
      (sixCameraWhitenedNaimarkSynthesis (Pi.single i 1))
      (globalNaimarkCameraProjection x) =
    inner ℝ
      (sixCameraWhitenedNaimarkSynthesis (Pi.single i 1)) x
  calc
    inner ℝ
        (sixCameraWhitenedNaimarkSynthesis (Pi.single i 1))
        (globalNaimarkCameraProjection x) =
      inner ℝ
        (globalNaimarkCameraProjection
          (sixCameraWhitenedNaimarkSynthesis (Pi.single i 1))) x :=
      (globalNaimarkCameraProjection_isSymmetric _ _).symm
    _ = inner ℝ
        (sixCameraWhitenedNaimarkSynthesis (Pi.single i 1)) x := by
      rw [globalNaimarkCameraProjection_fixes_sixCamera]

theorem synth_eq_sum_single (c : Fin 6 → ℝ) :
    sixCameraWhitenedNaimarkSynthesis c =
      ∑ i : Fin 6, c i • sixCameraWhitenedNaimarkSynthesis (Pi.single i 1) := by
  unfold sixCameraWhitenedNaimarkSynthesis sixCameraNaimarkSynthesis
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply,
    Finset.smul_sum, smul_smul]
  rw [← Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp
  rw [Finset.sum_smul]
  congr 1
  funext j
  ring_nf

theorem sixCameraWhitenedNaimarkSynthesis_inner_with
    (c : Fin 6 → ℝ) (x : NaimarkSpace) :
    inner ℝ (sixCameraWhitenedNaimarkSynthesis c) x =
      c ⬝ᵥ sixCameraWhitenedNaimarkAnalysis x := by
  classical
  rw [synth_eq_sum_single c]
  simp only [sum_inner, real_inner_smul_left]
  rfl

theorem sixCameraWhitenedNaimarkProjection_isSymmetric
    (x y : NaimarkSpace) :
    inner ℝ (sixCameraWhitenedNaimarkProjection x) y =
      inner ℝ x (sixCameraWhitenedNaimarkProjection y) := by
  rw [sixCameraWhitenedNaimarkProjection,
    sixCameraWhitenedNaimarkProjection,
    sixCameraWhitenedNaimarkSynthesis_inner_with,
    ← real_inner_comm,
    sixCameraWhitenedNaimarkSynthesis_inner_with,
    dotProduct_comm]

theorem globalNaimarkCameraEscape_isSymmetric :
    globalNaimarkCameraEscape.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (globalNaimarkCameraEscape x) y =
    inner ℝ x (globalNaimarkCameraEscape y)
  rw [globalNaimarkCameraEscape_apply, globalNaimarkCameraEscape_apply,
    inner_sub_left, inner_sub_right]
  rw [globalNaimarkCameraProjection_inner_symm]

theorem globalNaimarkCameraEscape_idempotent :
    globalNaimarkCameraEscape ∘L globalNaimarkCameraEscape =
      globalNaimarkCameraEscape := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply]
  rw [globalNaimarkCameraEscape_apply, globalNaimarkCameraEscape_apply,
    map_sub, globalNaimarkCameraProjection_idempotent_apply]
  simp

theorem globalNaimarkCameraEscape_isStarProjection :
    IsStarProjection globalNaimarkCameraEscape := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  refine ⟨?_, globalNaimarkCameraEscape_isSymmetric⟩
  change globalNaimarkCameraEscape.toLinearMap ∘ₗ
      globalNaimarkCameraEscape.toLinearMap =
    globalNaimarkCameraEscape.toLinearMap
  apply LinearMap.ext
  intro x
  change globalNaimarkCameraEscape
      (globalNaimarkCameraEscape x) =
    globalNaimarkCameraEscape x
  exact congrArg (fun T : NaimarkSpace →L[ℝ] NaimarkSpace => T x)
    globalNaimarkCameraEscape_idempotent

def sixCameraGlobalCoherentHaloProjection (x : NaimarkSpace) :
    NaimarkSpace :=
  globalNaimarkCameraProjection x -
    sixCameraWhitenedNaimarkProjection x

theorem sixCameraGlobalCoherentHaloProjection_apply (x : NaimarkSpace) :
    sixCameraGlobalCoherentHaloProjection x =
      globalNaimarkCameraProjection x -
        sixCameraWhitenedNaimarkProjection x := rfl

theorem globalNaimarkCameraProjection_sixCameraProjection (x : NaimarkSpace) :
    globalNaimarkCameraProjection
        (sixCameraWhitenedNaimarkProjection x) =
      sixCameraWhitenedNaimarkProjection x :=
  globalNaimarkCameraProjection_fixes_sixCameraProjection x

theorem sixCameraWhitenedNaimarkSynthesis_sub (c d : Fin 6 → ℝ) :
    sixCameraWhitenedNaimarkSynthesis (c - d) =
      sixCameraWhitenedNaimarkSynthesis c -
        sixCameraWhitenedNaimarkSynthesis d := by
  unfold sixCameraWhitenedNaimarkSynthesis sixCameraNaimarkSynthesis
  simp [Matrix.mulVec, dotProduct, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hscalar :
      (∑ x, positiveInverseSqrt sixCameraGram i x * (c x - d x)) =
        (∑ x, positiveInverseSqrt sixCameraGram i x * c x) -
          ∑ x, positiveInverseSqrt sixCameraGram i x * d x := by
    calc
      _ = ∑ x, (positiveInverseSqrt sixCameraGram i x * c x -
          positiveInverseSqrt sixCameraGram i x * d x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [hscalar, sub_smul]

theorem sixCameraWhitenedNaimarkAnalysis_sub (x y : NaimarkSpace) :
    sixCameraWhitenedNaimarkAnalysis (x - y) =
      sixCameraWhitenedNaimarkAnalysis x -
        sixCameraWhitenedNaimarkAnalysis y := by
  funext i
  unfold sixCameraWhitenedNaimarkAnalysis
  rw [inner_sub_right]
  rfl

theorem sixCameraWhitenedNaimarkProjection_sub (x y : NaimarkSpace) :
    sixCameraWhitenedNaimarkProjection (x - y) =
      sixCameraWhitenedNaimarkProjection x -
        sixCameraWhitenedNaimarkProjection y := by
  unfold sixCameraWhitenedNaimarkProjection
  rw [sixCameraWhitenedNaimarkAnalysis_sub,
    sixCameraWhitenedNaimarkSynthesis_sub]

theorem sixCameraGlobalCoherentHaloProjection_idempotent (x : NaimarkSpace) :
    sixCameraGlobalCoherentHaloProjection
        (sixCameraGlobalCoherentHaloProjection x) =
      sixCameraGlobalCoherentHaloProjection x := by
  unfold sixCameraGlobalCoherentHaloProjection
  rw [map_sub, globalNaimarkCameraProjection_idempotent_apply,
    globalNaimarkCameraProjection_sixCameraProjection,
    sixCameraWhitenedNaimarkProjection_sub,
    sixCameraProjection_globalNaimarkProjection,
    sixCameraWhitenedNaimarkProjection_idempotent]
  simp

theorem globalNaimarkCameraProjection_fixes_halo (x : NaimarkSpace) :
    globalNaimarkCameraProjection
        (sixCameraGlobalCoherentHaloProjection x) =
      sixCameraGlobalCoherentHaloProjection x := by
  unfold sixCameraGlobalCoherentHaloProjection
  rw [map_sub, globalNaimarkCameraProjection_idempotent_apply,
    globalNaimarkCameraProjection_sixCameraProjection]

theorem sixCameraWhitenedNaimarkProjection_annihilates_halo
    (x : NaimarkSpace) :
    sixCameraWhitenedNaimarkProjection
        (sixCameraGlobalCoherentHaloProjection x) = 0 := by
  unfold sixCameraGlobalCoherentHaloProjection
  rw [sixCameraWhitenedNaimarkProjection_sub,
    sixCameraProjection_globalNaimarkProjection,
    sixCameraWhitenedNaimarkProjection_idempotent]
  simp

theorem sixCameraGlobalCoherentHaloProjection_isSymmetric
    (x y : NaimarkSpace) :
    inner ℝ (sixCameraGlobalCoherentHaloProjection x) y =
      inner ℝ x (sixCameraGlobalCoherentHaloProjection y) := by
  rw [sixCameraGlobalCoherentHaloProjection_apply,
    sixCameraGlobalCoherentHaloProjection_apply,
    inner_sub_left, inner_sub_right]
  rw [globalNaimarkCameraProjection_inner_symm,
    sixCameraWhitenedNaimarkProjection_isSymmetric]

theorem globalNaimarkCameraEscape_inner_halo_eq_zero
    (x y : NaimarkSpace) :
    inner ℝ (globalNaimarkCameraEscape x)
      (sixCameraGlobalCoherentHaloProjection y) = 0 := by
  rw [globalNaimarkCameraEscape_apply,
    sixCameraGlobalCoherentHaloProjection_apply,
    inner_sub_sub_expansion]
  have h₁ :
      inner ℝ x (globalNaimarkCameraProjection y) =
        inner ℝ (globalNaimarkCameraProjection x)
          (globalNaimarkCameraProjection y) := by
    calc
      inner ℝ x (globalNaimarkCameraProjection y) =
          inner ℝ (globalNaimarkCameraProjection x) y := by
            exact (globalNaimarkCameraProjection_inner_symm x y).symm
      _ = inner ℝ (globalNaimarkCameraProjection x)
          (globalNaimarkCameraProjection y) := by
            have h := globalNaimarkCameraProjection_inner_symm
              (globalNaimarkCameraProjection x) y
            change inner ℝ (globalNaimarkCameraProjection
                (globalNaimarkCameraProjection x)) y =
              inner ℝ (globalNaimarkCameraProjection x)
                (globalNaimarkCameraProjection y) at h
            rw [globalNaimarkCameraProjection_idempotent_apply] at h
            exact h
  have h₂ :
      inner ℝ (globalNaimarkCameraProjection x)
          (globalNaimarkCameraProjection y) =
        inner ℝ (globalNaimarkCameraProjection x) y := by
    have h' := globalNaimarkCameraProjection_inner_symm
      (globalNaimarkCameraProjection x) y
    change inner ℝ (globalNaimarkCameraProjection
        (globalNaimarkCameraProjection x)) y =
      inner ℝ (globalNaimarkCameraProjection x)
        (globalNaimarkCameraProjection y) at h'
    rw [globalNaimarkCameraProjection_idempotent_apply] at h'
    exact h'.symm
  have h₃ :
      inner ℝ x (sixCameraWhitenedNaimarkProjection y) =
        inner ℝ (globalNaimarkCameraProjection x)
          (sixCameraWhitenedNaimarkProjection y) := by
    have h := globalNaimarkCameraProjection_inner_symm x
      (sixCameraWhitenedNaimarkProjection y)
    change inner ℝ (globalNaimarkCameraProjection x)
        (sixCameraWhitenedNaimarkProjection y) =
      inner ℝ x (globalNaimarkCameraProjection
        (sixCameraWhitenedNaimarkProjection y)) at h
    rw [globalNaimarkCameraProjection_sixCameraProjection] at h
    exact h.symm
  have h₄ :
      inner ℝ (globalNaimarkCameraProjection x)
          (sixCameraWhitenedNaimarkProjection y) =
        inner ℝ x (sixCameraWhitenedNaimarkProjection y) := by
    have h := globalNaimarkCameraProjection_inner_symm x
      (sixCameraWhitenedNaimarkProjection y)
    change inner ℝ (globalNaimarkCameraProjection x)
        (sixCameraWhitenedNaimarkProjection y) =
      inner ℝ x (globalNaimarkCameraProjection
        (sixCameraWhitenedNaimarkProjection y)) at h
    rw [globalNaimarkCameraProjection_sixCameraProjection] at h
    exact h
  linarith

theorem globalNaimarkCameraEscape_inner_halo_eq_zero'
    (x y : NaimarkSpace) :
    inner ℝ (sixCameraGlobalCoherentHaloProjection x)
      (globalNaimarkCameraEscape y) = 0 := by
  rw [real_inner_comm]
  exact globalNaimarkCameraEscape_inner_halo_eq_zero y x

theorem sixCameraEscape_eq_halo_add_globalEscape (x : NaimarkSpace) :
    sixCameraWhitenedNaimarkEscape x =
      sixCameraGlobalCoherentHaloProjection x +
        globalNaimarkCameraEscape x := by
  change x - sixCameraWhitenedNaimarkProjection x =
    (globalNaimarkCameraProjection x -
      sixCameraWhitenedNaimarkProjection x) +
      (x - globalNaimarkCameraProjection x)
  abel

theorem sixCameraEscape_inner_eq_globalHalo_add_globalEscape
    (x y : NaimarkSpace) :
    inner ℝ (sixCameraWhitenedNaimarkEscape x)
      (sixCameraWhitenedNaimarkEscape y) =
      inner ℝ (sixCameraGlobalCoherentHaloProjection x)
        (sixCameraGlobalCoherentHaloProjection y) +
        inner ℝ (globalNaimarkCameraEscape x)
          (globalNaimarkCameraEscape y) := by
  rw [sixCameraEscape_eq_halo_add_globalEscape,
    sixCameraEscape_eq_halo_add_globalEscape]
  simp only [inner_add_left, inner_add_right]
  have h₁ := globalNaimarkCameraEscape_inner_halo_eq_zero x y
  have h₂ := globalNaimarkCameraEscape_inner_halo_eq_zero' x y
  have h₃ := globalNaimarkCameraEscape_inner_halo_eq_zero' y x
  have h₄ := globalNaimarkCameraEscape_inner_halo_eq_zero y x
  linarith [h₁, h₂, h₃, h₄]

theorem sixCameraEscape_norm_sq_eq_globalHalo_add_globalEscape (x : NaimarkSpace) :
    ‖sixCameraWhitenedNaimarkEscape x‖ ^ 2 =
      ‖sixCameraGlobalCoherentHaloProjection x‖ ^ 2 +
        ‖globalNaimarkCameraEscape x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    sixCameraEscape_inner_eq_globalHalo_add_globalEscape,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem sixCameraVariance_eq_globalHaloGram_add_globalNaimarkEscapeGram
    (u v : Fin 6 → ℝ) :
    u ⬝ᵥ (sixCameraVariance *ᵥ v) =
      inner ℝ
          (sixCameraGlobalCoherentHaloProjection
            (sixCameraWhitenedCenteredLogNaimarkSynthesis u))
          (sixCameraGlobalCoherentHaloProjection
            (sixCameraWhitenedCenteredLogNaimarkSynthesis v)) +
      inner ℝ
          (globalNaimarkCameraEscape
            (sixCameraWhitenedCenteredLogNaimarkSynthesis u))
          (globalNaimarkCameraEscape
            (sixCameraWhitenedCenteredLogNaimarkSynthesis v)) := by
  rw [← sixCameraWhitenedNaimarkEscape_centeredLog_inner u v,
    sixCameraEscape_inner_eq_globalHalo_add_globalEscape]

theorem sixCameraVariance_norm_sq_eq_globalHalo_add_globalNaimarkEscape
    (u : Fin 6 → ℝ) :
    u ⬝ᵥ (sixCameraVariance *ᵥ u) =
      ‖sixCameraGlobalCoherentHaloProjection
          (sixCameraWhitenedCenteredLogNaimarkSynthesis u)‖ ^ 2 +
      ‖globalNaimarkCameraEscape
          (sixCameraWhitenedCenteredLogNaimarkSynthesis u)‖ ^ 2 := by
  rw [← sixCameraWhitenedNaimarkEscape_centeredLog_norm_sq u,
    sixCameraEscape_norm_sq_eq_globalHalo_add_globalEscape]

theorem sixCameraVariance_sqrt_norm_sq_eq_globalHalo_add_globalNaimarkEscape
    (u : Fin 6 → ℝ) :
    (CFC.sqrt sixCameraVariance *ᵥ u) ⬝ᵥ
        (CFC.sqrt sixCameraVariance *ᵥ u) =
      ‖sixCameraGlobalCoherentHaloProjection
          (sixCameraWhitenedCenteredLogNaimarkSynthesis u)‖ ^ 2 +
      ‖globalNaimarkCameraEscape
          (sixCameraWhitenedCenteredLogNaimarkSynthesis u)‖ ^ 2 := by
  rw [sixCameraWhitenedCenteredLog_variance_sqrt_pair,
    sixCameraVariance_norm_sq_eq_globalHalo_add_globalNaimarkEscape]


theorem synth_add (c d : Fin 6 → ℝ) :
    sixCameraWhitenedNaimarkSynthesis (c + d) =
      sixCameraWhitenedNaimarkSynthesis c +
        sixCameraWhitenedNaimarkSynthesis d := by
  unfold sixCameraWhitenedNaimarkSynthesis sixCameraNaimarkSynthesis
  simp [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hscalar :
      (∑ x, positiveInverseSqrt sixCameraGram i x * (c x + d x)) =
        (∑ x, positiveInverseSqrt sixCameraGram i x * c x) +
          ∑ x, positiveInverseSqrt sixCameraGram i x * d x := by
    calc
      _ = ∑ x, (positiveInverseSqrt sixCameraGram i x * c x +
          positiveInverseSqrt sixCameraGram i x * d x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = _ := by rw [Finset.sum_add_distrib]
  rw [hscalar, add_smul]

theorem synth_smul (a : ℝ) (c : Fin 6 → ℝ) :
    sixCameraWhitenedNaimarkSynthesis (a • c) =
      a • sixCameraWhitenedNaimarkSynthesis c := by
  unfold sixCameraWhitenedNaimarkSynthesis sixCameraNaimarkSynthesis
  simp [Matrix.mulVec, dotProduct, Pi.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hscalar :
      (∑ x, positiveInverseSqrt sixCameraGram i x * (a * c x)) =
        a * (∑ x, positiveInverseSqrt sixCameraGram i x * c x) := by
    calc
      _ = ∑ x, a * (positiveInverseSqrt sixCameraGram i x * c x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hscalar]
  rw [smul_smul]

def sixCameraWhitenedNaimarkSynthesisLinear :
    EuclideanSpace ℝ (Fin 6) →ₗ[ℝ] NaimarkSpace where
  toFun c := sixCameraWhitenedNaimarkSynthesis c.ofLp
  map_add' c d := by
    rw [show (c + d).ofLp = c.ofLp + d.ofLp by rfl, synth_add]
  map_smul' a c := by
    change sixCameraWhitenedNaimarkSynthesis ((a • c).ofLp) = _
    rw [show (a • c).ofLp = a • c.ofLp by rfl, synth_smul]
    rfl

 def sixCameraWhitenedNaimarkSynthesisIsometry :
    EuclideanSpace ℝ (Fin 6) →ₗᵢ[ℝ] NaimarkSpace where
  toLinearMap := sixCameraWhitenedNaimarkSynthesisLinear
  norm_map' c := by
    change ‖sixCameraWhitenedNaimarkSynthesis c.ofLp‖ = ‖c‖
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    rw [show inner ℝ (sixCameraWhitenedNaimarkSynthesis c.ofLp)
        (sixCameraWhitenedNaimarkSynthesis c.ofLp) =
        c.ofLp ⬝ᵥ c.ofLp by
          exact sixCameraWhitenedNaimarkSynthesis_inner c.ofLp c.ofLp]
    rfl

def sixCameraWhitenedNaimarkProjectionCLM :
    NaimarkSpace →L[ℝ] NaimarkSpace :=
  sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap ∘L
    (ContinuousLinearMap.adjoint
      sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap)

theorem sixCameraWhitenedNaimarkSynthesis_adjoint_apply (x : NaimarkSpace) :
    ((ContinuousLinearMap.adjoint
      sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x).ofLp =
      sixCameraWhitenedNaimarkAnalysis x := by
  funext i
  calc
    ((ContinuousLinearMap.adjoint
      sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x).ofLp i =
        inner ℝ (EuclideanSpace.basisFun (Fin 6) ℝ i)
          ((ContinuousLinearMap.adjoint
            sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x) := by
              rw [EuclideanSpace.basisFun_inner]
    _ = inner ℝ
          ((ContinuousLinearMap.adjoint
            sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x)
          (EuclideanSpace.basisFun (Fin 6) ℝ i) := by
            rw [real_inner_comm]
    _ = inner ℝ x
          (sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap
            (EuclideanSpace.basisFun (Fin 6) ℝ i)) := by
            exact ContinuousLinearMap.adjoint_inner_left
              sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap
              (EuclideanSpace.basisFun (Fin 6) ℝ i) x
    _ = inner ℝ
          (sixCameraWhitenedNaimarkSynthesis
            (Pi.single i 1)) x := by
            rw [EuclideanSpace.basisFun_apply]
            change inner ℝ x
                (sixCameraWhitenedNaimarkSynthesis (Pi.single i 1)) = _
            rw [real_inner_comm]
    _ = sixCameraWhitenedNaimarkAnalysis x i := rfl

theorem sixCameraWhitenedNaimarkProjectionCLM_apply (x : NaimarkSpace) :
    sixCameraWhitenedNaimarkProjectionCLM x =
      sixCameraWhitenedNaimarkProjection x := by
  change sixCameraWhitenedNaimarkSynthesis
      ((ContinuousLinearMap.adjoint
        sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x).ofLp = _
  rw [sixCameraWhitenedNaimarkSynthesis_adjoint_apply]
  rfl

theorem sixCameraWhitenedNaimarkSynthesis_adjoint_synthesis (c : EuclideanSpace ℝ (Fin 6)) :
    (ContinuousLinearMap.adjoint
      sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap)
        (sixCameraWhitenedNaimarkSynthesisIsometry c) = c := by
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact sixCameraWhitenedNaimarkSynthesisIsometry.inner_map_map z c

theorem sixCameraWhitenedNaimarkProjectionCLM_idempotent :
    sixCameraWhitenedNaimarkProjectionCLM ∘L
        sixCameraWhitenedNaimarkProjectionCLM =
      sixCameraWhitenedNaimarkProjectionCLM := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply]
  change sixCameraWhitenedNaimarkSynthesisIsometry
      ((ContinuousLinearMap.adjoint
        sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap)
        (sixCameraWhitenedNaimarkSynthesisIsometry
          ((ContinuousLinearMap.adjoint
            sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x))) = _
  rw [sixCameraWhitenedNaimarkSynthesis_adjoint_synthesis]
  rfl

theorem sixCameraWhitenedNaimarkProjectionCLM_isSymmetric :
    sixCameraWhitenedNaimarkProjectionCLM.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ
      (sixCameraWhitenedNaimarkProjectionCLM x) y =
    inner ℝ x (sixCameraWhitenedNaimarkProjectionCLM y)
  change inner ℝ
      (sixCameraWhitenedNaimarkSynthesisIsometry
        ((ContinuousLinearMap.adjoint
          sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x)) y =
    inner ℝ x
      (sixCameraWhitenedNaimarkSynthesisIsometry
        ((ContinuousLinearMap.adjoint
          sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) y))
  have hxy := ContinuousLinearMap.adjoint_inner_right
    sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap
    ((ContinuousLinearMap.adjoint
      sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x) y
  have hyx := ContinuousLinearMap.adjoint_inner_right
    sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap
    ((ContinuousLinearMap.adjoint
      sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) y) x
  calc
    inner ℝ
        (sixCameraWhitenedNaimarkSynthesisIsometry
          ((ContinuousLinearMap.adjoint
            sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x)) y =
        inner ℝ
          ((ContinuousLinearMap.adjoint
            sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x)
          ((ContinuousLinearMap.adjoint
            sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) y) := hxy.symm
    _ = inner ℝ
        ((ContinuousLinearMap.adjoint
          sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) y)
        ((ContinuousLinearMap.adjoint
          sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) x) := by
            rw [real_inner_comm]
    _ = inner ℝ x
        (sixCameraWhitenedNaimarkSynthesisIsometry
          ((ContinuousLinearMap.adjoint
            sixCameraWhitenedNaimarkSynthesisIsometry.toContinuousLinearMap) y)) := by
            simpa [real_inner_comm] using hyx

theorem sixCameraWhitenedNaimarkProjectionCLM_isStarProjection :
    IsStarProjection sixCameraWhitenedNaimarkProjectionCLM := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  refine ⟨?_, sixCameraWhitenedNaimarkProjectionCLM_isSymmetric⟩
  change sixCameraWhitenedNaimarkProjectionCLM.toLinearMap ∘ₗ
      sixCameraWhitenedNaimarkProjectionCLM.toLinearMap =
    sixCameraWhitenedNaimarkProjectionCLM.toLinearMap
  apply LinearMap.ext
  intro x
  exact congrArg (fun T : NaimarkSpace →L[ℝ] NaimarkSpace => T x)
    sixCameraWhitenedNaimarkProjectionCLM_idempotent



def sixCameraGlobalCoherentHaloProjectionCLM :
    NaimarkSpace →L[ℝ] NaimarkSpace :=
  globalNaimarkCameraProjection - sixCameraWhitenedNaimarkProjectionCLM

@[simp] theorem sixCameraGlobalCoherentHaloProjectionCLM_apply
    (x : NaimarkSpace) :
    sixCameraGlobalCoherentHaloProjectionCLM x =
      sixCameraGlobalCoherentHaloProjection x := by
  change globalNaimarkCameraProjection x -
      sixCameraWhitenedNaimarkProjectionCLM x = _
  rw [sixCameraWhitenedNaimarkProjectionCLM_apply]
  rfl

theorem globalNaimarkCameraProjection_sixCameraProjectionCLM :
    globalNaimarkCameraProjection ∘L sixCameraWhitenedNaimarkProjectionCLM =
      sixCameraWhitenedNaimarkProjectionCLM := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply,
    sixCameraWhitenedNaimarkProjectionCLM_apply]
  exact globalNaimarkCameraProjection_fixes_sixCameraProjection x

theorem sixCameraProjectionCLM_globalNaimarkProjection :
    sixCameraWhitenedNaimarkProjectionCLM ∘L globalNaimarkCameraProjection =
      sixCameraWhitenedNaimarkProjectionCLM := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply,
    sixCameraWhitenedNaimarkProjectionCLM_apply,
    sixCameraWhitenedNaimarkProjectionCLM_apply]
  exact sixCameraProjection_globalNaimarkProjection x

theorem sixCameraGlobalCoherentHaloProjectionCLM_idempotent :
    sixCameraGlobalCoherentHaloProjectionCLM ∘L
        sixCameraGlobalCoherentHaloProjectionCLM =
      sixCameraGlobalCoherentHaloProjectionCLM := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply]
  rw [sixCameraGlobalCoherentHaloProjectionCLM_apply]
  rw [sixCameraGlobalCoherentHaloProjectionCLM_apply]
  exact sixCameraGlobalCoherentHaloProjection_idempotent x

theorem sixCameraGlobalCoherentHaloProjectionCLM_isSymmetric :
    sixCameraGlobalCoherentHaloProjectionCLM.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (sixCameraGlobalCoherentHaloProjectionCLM x) y =
    inner ℝ x (sixCameraGlobalCoherentHaloProjectionCLM y)
  rw [sixCameraGlobalCoherentHaloProjectionCLM_apply,
    sixCameraGlobalCoherentHaloProjectionCLM_apply,
    sixCameraGlobalCoherentHaloProjection_isSymmetric]

theorem sixCameraGlobalCoherentHaloProjectionCLM_isStarProjection :
    IsStarProjection sixCameraGlobalCoherentHaloProjectionCLM := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  refine ⟨?_, sixCameraGlobalCoherentHaloProjectionCLM_isSymmetric⟩
  change sixCameraGlobalCoherentHaloProjectionCLM.toLinearMap ∘ₗ
      sixCameraGlobalCoherentHaloProjectionCLM.toLinearMap =
    sixCameraGlobalCoherentHaloProjectionCLM.toLinearMap
  apply LinearMap.ext
  intro x
  exact congrArg (fun T : NaimarkSpace →L[ℝ] NaimarkSpace => T x)
    sixCameraGlobalCoherentHaloProjectionCLM_idempotent



def sixCameraGlobalHaloWitnessCamera : CameraIndex := ⟨8, by norm_num⟩

def sixCameraGlobalHaloWitnessFinsupp (c : Fin 6 → ℝ) : CameraFinsupp :=
  ∑ i : Fin 6, Finsupp.single (atlasSixCameraIndex i) (c i)

lemma sixCameraGlobalHaloWitnessCamera_ne_six (i : Fin 6) :
    sixCameraGlobalHaloWitnessCamera ≠ atlasSixCameraIndex i := by
  intro h
  have hv : (8 : ℕ) = sixCamera i :=
    congrArg (fun c : CameraIndex => (c : ℕ)) h
  fin_cases i <;>
    norm_num [sixCameraGlobalHaloWitnessCamera, sixCamera] at hv

lemma sixCameraGlobalHaloWitnessFinsupp_apply_witness (c : Fin 6 → ℝ) :
    sixCameraGlobalHaloWitnessFinsupp c sixCameraGlobalHaloWitnessCamera = 0 := by
  unfold sixCameraGlobalHaloWitnessFinsupp
  change (∑ i : Fin 6,
    Finsupp.single (atlasSixCameraIndex i) (c i)
      sixCameraGlobalHaloWitnessCamera) = 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finsupp.single_eq_of_ne]
  exact sixCameraGlobalHaloWitnessCamera_ne_six i

lemma sixCameraGlobalHaloWitnessFinsupp_ne (c : Fin 6 → ℝ) :
    Finsupp.single sixCameraGlobalHaloWitnessCamera (1 : ℝ) ≠
      sixCameraGlobalHaloWitnessFinsupp c := by
  intro h
  have hv := congrArg (fun u : CameraFinsupp =>
    u sixCameraGlobalHaloWitnessCamera) h
  simp [sixCameraGlobalHaloWitnessFinsupp_apply_witness] at hv

lemma naimarkCoreMap_injective_witness : Function.Injective naimarkCoreMap := by
  intro u v h
  have hn : ‖u - v‖ = 0 := by
    rw [← naimarkCoreMap_norm]
    rw [map_sub, h, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma core_sum_single_witness (c : Fin 6 → ℝ) :
    naimarkCoreMap (sixCameraGlobalHaloWitnessFinsupp c) =
      sixCameraNaimarkSynthesis c := by
  unfold sixCameraGlobalHaloWitnessFinsupp sixCameraNaimarkSynthesis
  rw [map_sum]
  simp only [naimarkCoreMap_single]

lemma external_not_six_span_witness (c : Fin 6 → ℝ) :
    naimarkCameraVector sixCameraGlobalHaloWitnessCamera ≠
      sixCameraNaimarkSynthesis c := by
  intro h
  apply sixCameraGlobalHaloWitnessFinsupp_ne c
  apply naimarkCoreMap_injective_witness
  rw [core_sum_single_witness, naimarkCoreMap_single]
  simpa using h

theorem globalNaimarkCameraProjection_fixes_naimarkCameraVector
    (camera : CameraIndex) :
    globalNaimarkCameraProjection (naimarkCameraVector camera) =
      naimarkCameraVector camera := by
  rw [← naimarkIsometry_cameraVector]
  change naimarkIsometry
    (naimarkAdjoint (naimarkIsometry (cameraVector camera))) =
      naimarkIsometry (cameraVector camera)
  have hleft : naimarkAdjoint (naimarkIsometry (cameraVector camera)) =
      cameraVector camera := by
    change (naimarkAdjoint ∘L naimarkIsometry.toContinuousLinearMap)
      (cameraVector camera) = cameraVector camera
    rw [naimarkAdjoint_comp_naimarkIsometry]
    rfl
  rw [hleft]

theorem sixCameraGlobalCoherentHaloProjection_witness_ne_zero :
    sixCameraGlobalCoherentHaloProjection
        (naimarkCameraVector sixCameraGlobalHaloWitnessCamera) ≠ 0 := by
  intro hzero
  have hsub :
      globalNaimarkCameraProjection
          (naimarkCameraVector sixCameraGlobalHaloWitnessCamera) -
        sixCameraWhitenedNaimarkProjection
          (naimarkCameraVector sixCameraGlobalHaloWitnessCamera) = 0 := by
    simpa [sixCameraGlobalCoherentHaloProjection] using hzero
  have heq := sub_eq_zero.mp hsub
  have hp :
      naimarkCameraVector sixCameraGlobalHaloWitnessCamera =
        sixCameraWhitenedNaimarkProjection
          (naimarkCameraVector sixCameraGlobalHaloWitnessCamera) := by
    calc
      naimarkCameraVector sixCameraGlobalHaloWitnessCamera =
          globalNaimarkCameraProjection
            (naimarkCameraVector sixCameraGlobalHaloWitnessCamera) := by
              symm
              exact globalNaimarkCameraProjection_fixes_naimarkCameraVector _
      _ = sixCameraWhitenedNaimarkProjection
          (naimarkCameraVector sixCameraGlobalHaloWitnessCamera) := heq
  rw [sixCameraWhitenedNaimarkProjection] at hp
  exact external_not_six_span_witness _ hp



theorem sixCameraGlobalCoherentHaloProjectionCLM_witness_ne_zero :
    sixCameraGlobalCoherentHaloProjectionCLM
        (naimarkCameraVector sixCameraGlobalHaloWitnessCamera) ≠ 0 := by
  rw [sixCameraGlobalCoherentHaloProjectionCLM_apply]
  exact sixCameraGlobalCoherentHaloProjection_witness_ne_zero

theorem sixCameraGlobalCoherentHaloProjectionCLM_ne_zero :
    sixCameraGlobalCoherentHaloProjectionCLM ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun T : NaimarkSpace →L[ℝ] NaimarkSpace =>
      T (naimarkCameraVector sixCameraGlobalHaloWitnessCamera)) hzero
  exact sixCameraGlobalCoherentHaloProjectionCLM_witness_ne_zero h

end
end CarrySelfAdjointOperator

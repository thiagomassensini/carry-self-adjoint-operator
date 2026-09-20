import CarrySelfAdjointOperator.CompletedNativeAllCameraPortAmbientNoGo
import Mathlib.Tactic

/-!
# Six-camera projection test on the normalized ambient state

The global all-camera Naimark escape is identically zero on the completed
ambient response.  This module consequently tests the strictly smaller,
historical whitened six-camera projection already constructed from the six
camera Gram.  Its complementary output is the coherent all-camera halo on
the actual response (the global escape remains zero).

No equality with the completed-native moment is assumed.  Instead, the
central excess residual is reduced exactly to one concrete question: whether
the energy visible to the historical whitened six-camera projection equals
the zeroth completed-native moment.
-/

open scoped InnerProductSpace

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## Real and two-quadrature six-camera projection -/

/-- Orthogonality of the concrete whitened six-camera projection and its
complement in the native real Naimark space. -/
theorem inner_sixCameraWhitenedNaimarkProjection_sub_eq_zero
    (x y : NaimarkSpace) :
    inner ℝ (sixCameraWhitenedNaimarkProjectionCLM x)
      (y - sixCameraWhitenedNaimarkProjectionCLM y) = 0 := by
  have h := sixCameraWhitenedNaimarkProjectionCLM_isSymmetric x
    (y - sixCameraWhitenedNaimarkProjectionCLM y)
  change inner ℝ (sixCameraWhitenedNaimarkProjectionCLM x)
      (y - sixCameraWhitenedNaimarkProjectionCLM y) =
    inner ℝ x
      (sixCameraWhitenedNaimarkProjectionCLM
        (y - sixCameraWhitenedNaimarkProjectionCLM y)) at h
  have hidempotent :
      sixCameraWhitenedNaimarkProjectionCLM
          (sixCameraWhitenedNaimarkProjectionCLM y) =
        sixCameraWhitenedNaimarkProjectionCLM y := by
    exact congrArg (fun T : NaimarkSpace →L[ℝ] NaimarkSpace => T y)
      sixCameraWhitenedNaimarkProjectionCLM_idempotent
  rw [map_sub, hidempotent, sub_self, inner_zero_right] at h
  exact h

/-- Polarized Pythagoras for the actual historical whitened six-camera
projection. -/
theorem inner_sixCameraWhitenedNaimark_eq_projection_add_escape
    (x y : NaimarkSpace) :
    inner ℝ x y =
      inner ℝ (sixCameraWhitenedNaimarkProjectionCLM x)
        (sixCameraWhitenedNaimarkProjectionCLM y) +
      inner ℝ (x - sixCameraWhitenedNaimarkProjectionCLM x)
        (y - sixCameraWhitenedNaimarkProjectionCLM y) := by
  have hleft := inner_sixCameraWhitenedNaimarkProjection_sub_eq_zero x y
  have hright :
      inner ℝ (x - sixCameraWhitenedNaimarkProjectionCLM x)
        (sixCameraWhitenedNaimarkProjectionCLM y) = 0 := by
    rw [real_inner_comm]
    exact inner_sixCameraWhitenedNaimarkProjection_sub_eq_zero y x
  calc
    inner ℝ x y =
        inner ℝ
          (sixCameraWhitenedNaimarkProjectionCLM x +
            (x - sixCameraWhitenedNaimarkProjectionCLM x))
          (sixCameraWhitenedNaimarkProjectionCLM y +
            (y - sixCameraWhitenedNaimarkProjectionCLM y)) := by
      congr 1 <;> abel
    _ =
        inner ℝ (sixCameraWhitenedNaimarkProjectionCLM x)
          (sixCameraWhitenedNaimarkProjectionCLM y) +
        inner ℝ (x - sixCameraWhitenedNaimarkProjectionCLM x)
          (y - sixCameraWhitenedNaimarkProjectionCLM y) := by
      simp_rw [inner_add_left, inner_add_right]
      rw [hleft, hright]
      ring

/-- Coordinatewise realification of the concrete six-camera orthogonal
projection.  The zero imaginary operator is intentional: this is the
complexification of a real geometric projector, not a fitted complex map. -/
def canonicalCompletedC3SixCameraProjection :
    RealifiedNaimarkComplexification →L[ℝ]
      RealifiedNaimarkComplexification :=
  realifiedContinuousLinearBlock sixCameraWhitenedNaimarkProjectionCLM 0

@[simp] theorem canonicalCompletedC3SixCameraProjection_fst
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3SixCameraProjection x).fst =
      sixCameraWhitenedNaimarkProjectionCLM x.fst := by
  unfold canonicalCompletedC3SixCameraProjection
  rw [realifiedContinuousLinearBlock_fst]
  simp

@[simp] theorem canonicalCompletedC3SixCameraProjection_snd
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3SixCameraProjection x).snd =
      sixCameraWhitenedNaimarkProjectionCLM x.snd := by
  unfold canonicalCompletedC3SixCameraProjection
  rw [realifiedContinuousLinearBlock_snd]
  simp

/-- Complement of the historical six-camera projector, still before the
canonical complex Hilbert view. -/
def canonicalCompletedC3SixCameraHorizontalProjection :
    RealifiedNaimarkComplexification →L[ℝ]
      RealifiedNaimarkComplexification :=
  (1 : RealifiedNaimarkComplexification →L[ℝ]
      RealifiedNaimarkComplexification) -
    canonicalCompletedC3SixCameraProjection

/-- Coordinatewise realification of the pre-existing coherent global halo
projection `P_global - P_six`. -/
def canonicalCompletedC3SixCameraGlobalHaloProjection :
    RealifiedNaimarkComplexification →L[ℝ]
      RealifiedNaimarkComplexification :=
  realifiedContinuousLinearBlock sixCameraGlobalCoherentHaloProjectionCLM 0

@[simp] theorem canonicalCompletedC3SixCameraGlobalHaloProjection_fst
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3SixCameraGlobalHaloProjection x).fst =
      sixCameraGlobalCoherentHaloProjectionCLM x.fst := by
  unfold canonicalCompletedC3SixCameraGlobalHaloProjection
  rw [realifiedContinuousLinearBlock_fst]
  simp

@[simp] theorem canonicalCompletedC3SixCameraGlobalHaloProjection_snd
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3SixCameraGlobalHaloProjection x).snd =
      sixCameraGlobalCoherentHaloProjectionCLM x.snd := by
  unfold canonicalCompletedC3SixCameraGlobalHaloProjection
  rw [realifiedContinuousLinearBlock_snd]
  simp

@[simp] theorem canonicalCompletedC3SixCameraHorizontalProjection_fst
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3SixCameraHorizontalProjection x).fst =
      x.fst - sixCameraWhitenedNaimarkProjectionCLM x.fst := by
  unfold canonicalCompletedC3SixCameraHorizontalProjection
  simp

@[simp] theorem canonicalCompletedC3SixCameraHorizontalProjection_snd
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3SixCameraHorizontalProjection x).snd =
      x.snd - sixCameraWhitenedNaimarkProjectionCLM x.snd := by
  unfold canonicalCompletedC3SixCameraHorizontalProjection
  simp

/-! ## Polarized lossless splitting in the ambient complex carrier -/

/-- The six-camera projection and its horizontal complement form a
polarized lossless splitting after the canonical complex Hilbert view. -/
theorem inner_canonicalCompletedC3GammaNaimarkView_eq_sixCameraProjection_add_horizontal
    (x y : RealifiedNaimarkComplexification) :
    inner ℂ (canonicalCompletedC3GammaNaimarkView x)
        (canonicalCompletedC3GammaNaimarkView y) =
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3SixCameraProjection x))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3SixCameraProjection y)) +
        inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3SixCameraHorizontalProjection x))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3SixCameraHorizontalProjection y)) := by
  apply Complex.ext
  · simp only [canonicalCompletedC3GammaNaimarkView,
      RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      Complex.add_re]
    change inner ℝ x.fst y.fst + inner ℝ x.snd y.snd =
      (inner ℝ (canonicalCompletedC3SixCameraProjection x).fst
          (canonicalCompletedC3SixCameraProjection y).fst +
        inner ℝ (canonicalCompletedC3SixCameraProjection x).snd
          (canonicalCompletedC3SixCameraProjection y).snd) +
      (inner ℝ (canonicalCompletedC3SixCameraHorizontalProjection x).fst
          (canonicalCompletedC3SixCameraHorizontalProjection y).fst +
        inner ℝ (canonicalCompletedC3SixCameraHorizontalProjection x).snd
          (canonicalCompletedC3SixCameraHorizontalProjection y).snd)
    rw [canonicalCompletedC3SixCameraProjection_fst x,
      canonicalCompletedC3SixCameraProjection_fst y,
      canonicalCompletedC3SixCameraProjection_snd x,
      canonicalCompletedC3SixCameraProjection_snd y,
      canonicalCompletedC3SixCameraHorizontalProjection_fst x,
      canonicalCompletedC3SixCameraHorizontalProjection_fst y,
      canonicalCompletedC3SixCameraHorizontalProjection_snd x,
      canonicalCompletedC3SixCameraHorizontalProjection_snd y]
    have hfst :=
      inner_sixCameraWhitenedNaimark_eq_projection_add_escape x.fst y.fst
    have hsnd :=
      inner_sixCameraWhitenedNaimark_eq_projection_add_escape x.snd y.snd
    rw [hfst, hsnd]
    ring
  · simp only [canonicalCompletedC3GammaNaimarkView,
      RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_im,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      Complex.add_im]
    change inner ℝ x.fst y.snd - inner ℝ x.snd y.fst =
      (inner ℝ (canonicalCompletedC3SixCameraProjection x).fst
          (canonicalCompletedC3SixCameraProjection y).snd -
        inner ℝ (canonicalCompletedC3SixCameraProjection x).snd
          (canonicalCompletedC3SixCameraProjection y).fst) +
      (inner ℝ (canonicalCompletedC3SixCameraHorizontalProjection x).fst
          (canonicalCompletedC3SixCameraHorizontalProjection y).snd -
        inner ℝ (canonicalCompletedC3SixCameraHorizontalProjection x).snd
          (canonicalCompletedC3SixCameraHorizontalProjection y).fst)
    rw [canonicalCompletedC3SixCameraProjection_fst x,
      canonicalCompletedC3SixCameraProjection_fst y,
      canonicalCompletedC3SixCameraProjection_snd x,
      canonicalCompletedC3SixCameraProjection_snd y,
      canonicalCompletedC3SixCameraHorizontalProjection_fst x,
      canonicalCompletedC3SixCameraHorizontalProjection_fst y,
      canonicalCompletedC3SixCameraHorizontalProjection_snd x,
      canonicalCompletedC3SixCameraHorizontalProjection_snd y]
    have h₁ :=
      inner_sixCameraWhitenedNaimark_eq_projection_add_escape x.fst y.snd
    have h₂ :=
      inner_sixCameraWhitenedNaimark_eq_projection_add_escape x.snd y.fst
    rw [h₁, h₂]
    ring

/-! ## The actual normalized state and central residual -/

/-- Visible six-camera output for the actual normalized ambient input. -/
def canonicalCompletedC3NormalizedAmbientSixCameraVisibleState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (canonicalCompletedC3SixCameraProjection
      (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf))

/-- Horizontal/halo output of the same historical six-camera projection for
the actual normalized ambient input. -/
def canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (canonicalCompletedC3SixCameraHorizontalProjection
      (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf))

/-- The same complementary output, named directly as the pre-existing
coherent global halo rather than as a newly chosen defect channel. -/
def canonicalCompletedC3NormalizedAmbientSixCameraGlobalHaloState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (canonicalCompletedC3SixCameraGlobalHaloProjection
      (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf))

/-- On the actual normalized ambient state, the six-camera complement is
exactly the coherent global halo.  The global Naimark escape is absent by the
previous all-camera-port no-go, so no third hidden component remains. -/
theorem canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState_eq_globalHalo
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState z hzHalf =
      canonicalCompletedC3NormalizedAmbientSixCameraGlobalHaloState z hzHalf := by
  apply RealHilbertComplexification.ext
  · change
      (canonicalCompletedC3SixCameraHorizontalProjection
          (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf)).fst =
        (canonicalCompletedC3SixCameraGlobalHaloProjection
          (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf)).fst
    rw [canonicalCompletedC3SixCameraHorizontalProjection_fst,
      canonicalCompletedC3SixCameraGlobalHaloProjection_fst,
      sixCameraGlobalCoherentHaloProjectionCLM_apply,
      sixCameraWhitenedNaimarkProjectionCLM_apply,
      sixCameraGlobalCoherentHaloProjection_apply]
    have hfix := congrArg (fun x : RealifiedNaimarkComplexification => x.fst)
      (canonicalCompletedC3AmbientPortProjection_normalizedAmbientRealifiedState z hzHalf)
    rw [canonicalCompletedC3AmbientPortProjection_fst_eq_globalNaimarkCameraProjection]
      at hfix
    rw [hfix]
  · change
      (canonicalCompletedC3SixCameraHorizontalProjection
          (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf)).snd =
        (canonicalCompletedC3SixCameraGlobalHaloProjection
          (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf)).snd
    rw [canonicalCompletedC3SixCameraHorizontalProjection_snd,
      canonicalCompletedC3SixCameraGlobalHaloProjection_snd,
      sixCameraGlobalCoherentHaloProjectionCLM_apply,
      sixCameraWhitenedNaimarkProjectionCLM_apply,
      sixCameraGlobalCoherentHaloProjection_apply]
    have hfix := congrArg (fun x : RealifiedNaimarkComplexification => x.snd)
      (canonicalCompletedC3AmbientPortProjection_normalizedAmbientRealifiedState z hzHalf)
    rw [canonicalCompletedC3AmbientPortProjection_snd_eq_globalNaimarkCameraProjection]
      at hfix
    rw [hfix]

/-- All-order polarized energy conservation for the actual normalized
ambient state under the historical six-camera splitting. -/
theorem inner_canonicalCompletedC3NormalizedAmbientResponseState_eq_sixCameraVisible_add_horizontal
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    inner ℂ (canonicalCompletedC3NormalizedAmbientResponseState z hzHalf)
        (canonicalCompletedC3NormalizedAmbientResponseState w hwHalf) =
      inner ℂ (canonicalCompletedC3NormalizedAmbientSixCameraVisibleState z hzHalf)
          (canonicalCompletedC3NormalizedAmbientSixCameraVisibleState w hwHalf) +
        inner ℂ (canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState z hzHalf)
          (canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState w hwHalf) := by
  rw [← canonicalCompletedC3GammaNaimarkView_normalizedAmbientRealifiedState,
    ← canonicalCompletedC3GammaNaimarkView_normalizedAmbientRealifiedState]
  exact inner_canonicalCompletedC3GammaNaimarkView_eq_sixCameraProjection_add_horizontal _ _

/-- The all-order complement is not an abstract remainder: on the actual
ambient state it is precisely the pre-existing coherent global halo. -/
theorem inner_canonicalCompletedC3NormalizedAmbientResponseState_eq_sixCameraVisible_add_globalHalo
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    inner ℂ (canonicalCompletedC3NormalizedAmbientResponseState z hzHalf)
        (canonicalCompletedC3NormalizedAmbientResponseState w hwHalf) =
      inner ℂ (canonicalCompletedC3NormalizedAmbientSixCameraVisibleState z hzHalf)
          (canonicalCompletedC3NormalizedAmbientSixCameraVisibleState w hwHalf) +
        inner ℂ (canonicalCompletedC3NormalizedAmbientSixCameraGlobalHaloState z hzHalf)
          (canonicalCompletedC3NormalizedAmbientSixCameraGlobalHaloState w hwHalf) := by
  rw [inner_canonicalCompletedC3NormalizedAmbientResponseState_eq_sixCameraVisible_add_horizontal,
    canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState_eq_globalHalo,
    canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState_eq_globalHalo]

/-- Exact central residual of the concrete six-camera horizontal candidate. -/
def canonicalCompletedC3SixCameraHorizontalCentralExcessResidual : ℝ :=
  ‖canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState 0
      (by norm_num [operatorHeightParameter])‖ ^ 2 -
    canonicalCompletedC3NormalizedAmbientCentralExcess

/-- The central residual reduces exactly to the native zeroth moment minus
the actual six-camera-visible energy.  Thus the desired equality of the
horizontal energy with the ambient excess is equivalent to a single visible
energy identity, with neither side defined through a target PSD statement. -/
theorem canonicalCompletedC3SixCameraHorizontalCentralExcessResidual_eq_moment_sub_visible :
    canonicalCompletedC3SixCameraHorizontalCentralExcessResidual =
      canonicalCompletedNativeLogDerivativeMoment 0 -
        ‖canonicalCompletedC3NormalizedAmbientSixCameraVisibleState 0
          (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  unfold canonicalCompletedC3SixCameraHorizontalCentralExcessResidual
    canonicalCompletedC3NormalizedAmbientCentralExcess
  have hsplitComplex :=
    inner_canonicalCompletedC3NormalizedAmbientResponseState_eq_sixCameraVisible_add_horizontal
      0 0 (by norm_num [operatorHeightParameter])
      (by norm_num [operatorHeightParameter])
  have hsplit :
      ‖canonicalCompletedC3NormalizedAmbientResponseState 0
          (by norm_num [operatorHeightParameter])‖ ^ 2 =
        ‖canonicalCompletedC3NormalizedAmbientSixCameraVisibleState 0
          (by norm_num [operatorHeightParameter])‖ ^ 2 +
        ‖canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState 0
          (by norm_num [operatorHeightParameter])‖ ^ 2 := by
    have hreal := congrArg Complex.re hsplitComplex
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K] at hreal
    norm_cast at hreal
  linarith

/-- Central energy matching for the six-camera horizontal candidate is
equivalent to the concrete six-camera visible energy being the zeroth native
moment. -/
theorem canonicalCompletedC3SixCameraHorizontal_central_energy_eq_excess_iff :
    ‖canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState 0
        (by norm_num [operatorHeightParameter])‖ ^ 2 =
      canonicalCompletedC3NormalizedAmbientCentralExcess ↔
    ‖canonicalCompletedC3NormalizedAmbientSixCameraVisibleState 0
        (by norm_num [operatorHeightParameter])‖ ^ 2 =
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  constructor
  · intro henergy
    have hres : canonicalCompletedC3SixCameraHorizontalCentralExcessResidual = 0 := by
      unfold canonicalCompletedC3SixCameraHorizontalCentralExcessResidual
      exact sub_eq_zero.mpr henergy
    rw [canonicalCompletedC3SixCameraHorizontalCentralExcessResidual_eq_moment_sub_visible,
      sub_eq_zero] at hres
    exact hres.symm
  · intro hvisible
    have hres : canonicalCompletedC3SixCameraHorizontalCentralExcessResidual = 0 := by
      rw [canonicalCompletedC3SixCameraHorizontalCentralExcessResidual_eq_moment_sub_visible,
        sub_eq_zero]
      exact hvisible.symm
    unfold canonicalCompletedC3SixCameraHorizontalCentralExcessResidual at hres
    exact sub_eq_zero.mp hres

end

end CarrySelfAdjointOperator

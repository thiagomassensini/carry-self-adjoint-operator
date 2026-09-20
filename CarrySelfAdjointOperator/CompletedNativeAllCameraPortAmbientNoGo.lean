import CarrySelfAdjointOperator.CompletedNativeCameraVerticalHorizontalEnergyCrosswalk
import CarrySelfAdjointOperator.CompletedC3NaimarkCoisometricBlock
import CarrySelfAdjointOperator.SixCameraGlobalNaimarkHaloDecomposition
import Mathlib.Tactic

/-!
# No-go for the canonical all-camera Naimark port as the ambient defect

The literal normalized ambient Gram remains closed as a no-go; this module
does not alter it.  It instead tests one concrete, pre-existing geometric
candidate for the requested vertical/horizontal split: the canonical
all-camera Naimark port

`canonicalCompletedC3AmbientPortProjection = U U*`.

This is an actual historical all-camera projection, with a genuine lossless
port-plus-escape block.  The test is nevertheless negative for the present
purpose.  The completed ambient response already lies in its range.  After
the same `sqrt 2 * F` normalization, the proposed horizontal/escape output
is therefore identically zero.  Since the normalized ambient central excess
is strictly positive, this particular global port/escape splitting cannot
realize that excess.

This eliminates only the concrete all-camera Naimark port candidate below.
It neither changes the finite historical camera projection audit nor rules
out a different geometric bridge from a finite/multibase camera state into
the ambient carrier.
-/

open scoped InnerProductSpace

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## The normalized all-camera port candidate -/

/-- The first quadrature of the completed-C3 ambient port is literally the
already-named global historical camera projection `U U*`.  This makes the
candidate below a use of that existing global projection, not a surrogate
introduced for the excess test. -/
theorem canonicalCompletedC3AmbientPortProjection_fst_eq_globalNaimarkCameraProjection
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3AmbientPortProjection x).fst =
      globalNaimarkCameraProjection x.fst := by
  simp only [canonicalCompletedC3AmbientPortProjection,
    ContinuousLinearMap.comp_apply, realifiedNaimarkPort_fst,
    realifiedNaimarkAdjoint_fst]
  change naimarkIsometry (naimarkAdjoint x.fst) =
    globalNaimarkCameraProjection x.fst
  rfl

/-- The same global historical camera projection acts on the second
quadrature of the realification. -/
theorem canonicalCompletedC3AmbientPortProjection_snd_eq_globalNaimarkCameraProjection
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3AmbientPortProjection x).snd =
      globalNaimarkCameraProjection x.snd := by
  simp only [canonicalCompletedC3AmbientPortProjection,
    ContinuousLinearMap.comp_apply, realifiedNaimarkPort_snd,
    realifiedNaimarkAdjoint_snd]
  change naimarkIsometry (naimarkAdjoint x.snd) =
    globalNaimarkCameraProjection x.snd
  rfl

/-- The scalar used by the existing normalized ambient response.  Naming it
here makes explicit that the candidate uses no fitted rescaling. -/
def canonicalCompletedC3NormalizedAmbientScalar (z : ℂ) : ℂ :=
  ((((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic z)⁻¹)

/-- The same normalized ambient vector, retained in the native realified
carrier before taking its canonical complex Hilbert view. -/
def canonicalCompletedC3NormalizedAmbientRealifiedState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    RealifiedNaimarkComplexification :=
  realifiedNaimarkScalar (canonicalCompletedC3NormalizedAmbientScalar z)
    (completedC3SymplecticNaimarkState (operatorHeightParameter z) hzHalf)

/-- The visible output of the concrete all-camera Naimark projection applied
to the actual normalized ambient state. -/
def canonicalCompletedC3NormalizedAmbientAllCameraPortState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (canonicalCompletedC3AmbientPortProjection
      (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf))

/-- The only intrinsic complementary output supplied by the same concrete
all-camera lossless block.  This is the candidate horizontal/gauge channel
being tested, rather than a new factorization. -/
def canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf -
      canonicalCompletedC3AmbientPortProjection
        (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf))

/-- The native realified state is exactly the existing normalized complex
ambient state when viewed in its canonical complex Hilbert structure. -/
theorem canonicalCompletedC3GammaNaimarkView_normalizedAmbientRealifiedState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf) =
      canonicalCompletedC3NormalizedAmbientResponseState z hzHalf := by
  let a : ℂ := canonicalCompletedC3NormalizedAmbientScalar z
  let u : RealifiedNaimarkComplexification :=
    completedC3SymplecticNaimarkState (operatorHeightParameter z) hzHalf
  change canonicalCompletedC3GammaNaimarkView (realifiedNaimarkScalar a u) =
    a • canonicalCompletedC3GammaNaimarkView u
  exact canonicalCompletedC3GammaNaimarkView_realifiedNaimarkScalar a u

/-- The all-camera port fixes the normalized realified ambient response.
This is inherited from the completed ambient state already being a promoted
camera vector; it is not a positivity argument. -/
theorem canonicalCompletedC3AmbientPortProjection_normalizedAmbientRealifiedState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientPortProjection
        (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf) =
      canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf := by
  unfold canonicalCompletedC3NormalizedAmbientRealifiedState
  rw [canonicalCompletedC3AmbientPortProjection_realifiedNaimarkScalar,
    canonicalCompletedC3AmbientPortProjection_completedSymplecticState]

/-- The visible output of this global candidate is the entire normalized
ambient state. -/
theorem canonicalCompletedC3NormalizedAmbientAllCameraPortState_eq_response
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3NormalizedAmbientAllCameraPortState z hzHalf =
      canonicalCompletedC3NormalizedAmbientResponseState z hzHalf := by
  unfold canonicalCompletedC3NormalizedAmbientAllCameraPortState
  rw [canonicalCompletedC3AmbientPortProjection_normalizedAmbientRealifiedState]
  exact canonicalCompletedC3GammaNaimarkView_normalizedAmbientRealifiedState _ _

/-- The complementary output of the canonical all-camera lossless block
vanishes identically.  Thus this channel fails before any radial or
multi-point comparison: it has no central energy at all. -/
theorem canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState_eq_zero
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState z hzHalf = 0 := by
  unfold canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState
  rw [canonicalCompletedC3AmbientPortProjection_normalizedAmbientRealifiedState]
  simp

/-- The proposed all-camera port/horizontal pair still gives a literal
lossless polarized splitting of the normalized ambient response, but its
second summand is the zero channel. -/
theorem inner_canonicalCompletedC3NormalizedAmbientResponseState_eq_allCameraPort_add_horizontal
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    inner ℂ (canonicalCompletedC3NormalizedAmbientResponseState z hzHalf)
        (canonicalCompletedC3NormalizedAmbientResponseState w hwHalf) =
      inner ℂ (canonicalCompletedC3NormalizedAmbientAllCameraPortState z hzHalf)
          (canonicalCompletedC3NormalizedAmbientAllCameraPortState w hwHalf) +
        inner ℂ (canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState z hzHalf)
          (canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState w hwHalf) := by
  rw [canonicalCompletedC3NormalizedAmbientAllCameraPortState_eq_response,
    canonicalCompletedC3NormalizedAmbientAllCameraPortState_eq_response,
    canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState_eq_zero,
    canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState_eq_zero]
  simp

/-! ## Central mismatch with the positive ambient excess -/

/-- Exact central residual for the concrete all-camera horizontal candidate:
candidate horizontal energy minus the already-defined ambient excess. -/
def canonicalCompletedC3AllCameraHorizontalCentralExcessResidual : ℝ :=
  ‖canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState 0
      (by norm_num [operatorHeightParameter])‖ ^ 2 -
    canonicalCompletedC3NormalizedAmbientCentralExcess

/-- The candidate residual is exactly the negative of the positive excess. -/
theorem canonicalCompletedC3AllCameraHorizontalCentralExcessResidual_eq_neg :
    canonicalCompletedC3AllCameraHorizontalCentralExcessResidual =
      -canonicalCompletedC3NormalizedAmbientCentralExcess := by
  unfold canonicalCompletedC3AllCameraHorizontalCentralExcessResidual
  rw [canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState_eq_zero]
  simp

/-- The central residual is strictly negative.  Hence the historical
all-camera Naimark escape cannot be the requested horizontal/gauge energy. -/
theorem canonicalCompletedC3AllCameraHorizontalCentralExcessResidual_neg :
    canonicalCompletedC3AllCameraHorizontalCentralExcessResidual < 0 := by
  rw [canonicalCompletedC3AllCameraHorizontalCentralExcessResidual_eq_neg]
  exact neg_lt_zero.mpr canonicalCompletedC3NormalizedAmbientCentralExcess_pos

/-- Explicit candidate-specific no-go: the all-camera horizontal energy at
the centre is not the normalized ambient central excess. -/
theorem canonicalCompletedC3AllCameraHorizontal_central_energy_ne_excess :
    ‖canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState 0
        (by norm_num [operatorHeightParameter])‖ ^ 2 ≠
      canonicalCompletedC3NormalizedAmbientCentralExcess := by
  intro h
  have hzero : canonicalCompletedC3AllCameraHorizontalCentralExcessResidual = 0 := by
    unfold canonicalCompletedC3AllCameraHorizontalCentralExcessResidual
    exact sub_eq_zero.mpr h
  have hneg := canonicalCompletedC3AllCameraHorizontalCentralExcessResidual_neg
  linarith

end

end CarrySelfAdjointOperator

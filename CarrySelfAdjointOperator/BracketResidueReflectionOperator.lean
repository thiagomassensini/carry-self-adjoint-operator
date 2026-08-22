import CarrySelfAdjointOperator.BracketResidueOrbit
import NativeCarrySpectralWeyl.Infinite.GramKernel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Reflection operator on the cyclic bracket channels

Every supported camera residue quotient carries the canonical reflection
`a ↦ -a`.  Pullback along this reflection acts on the finite Euclidean space
of residue signals.  The pullback is an isometric symmetric involution, hence
its `+1` and `-1` parts are complementary orthogonal projections.

The native centered bracket occupies the even sector: its two leg impulses
are exchanged and its center impulse is fixed.  The oriented leg difference
occupies the odd sector.  At an antipodal radius the odd leg signal vanishes,
exactly matching the collapse of the two-channel reflection orbit.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Every supported camera has a nonzero cyclic modulus. -/
instance cameraSlope_neZero (camera : CameraIndex) :
    NeZero (cameraSlope (cameraLabel camera)) :=
  ⟨Nat.ne_of_gt (cameraSlope_pos camera)⟩

/-- Real Hilbert space of signals on the cyclic channel set of one supported
camera. -/
abbrev CameraResidueSignal (camera : CameraIndex) :=
  EuclideanSpace ℝ (ZMod (cameraSlope (cameraLabel camera)))

/-- Pullback of a residue signal along the canonical channel reflection. -/
def cameraResidueReflectionOperator (camera : CameraIndex) :
    CameraResidueSignal camera →ₗ[ℝ] CameraResidueSignal camera where
  toFun signal := WithLp.toLp 2 (fun channel ↦
    signal (cameraResidueReflection (cameraLabel camera) channel))
  map_add' := by
    intro first second
    ext channel
    simp
  map_smul' := by
    intro scalar signal
    ext channel
    simp

@[simp] theorem cameraResidueReflectionOperator_apply
    (camera : CameraIndex) (signal : CameraResidueSignal camera)
    (channel : ZMod (cameraSlope (cameraLabel camera))) :
    cameraResidueReflectionOperator camera signal channel = signal (-channel) :=
  rfl

/-- Pullback reflection is an involution on the entire signal space. -/
theorem cameraResidueReflectionOperator_involutive (camera : CameraIndex) :
    Function.Involutive (cameraResidueReflectionOperator camera) := by
  intro signal
  ext channel
  simp

/-- Operator form of the involution identity. -/
theorem cameraResidueReflectionOperator_sq (camera : CameraIndex) :
    cameraResidueReflectionOperator camera *
        cameraResidueReflectionOperator camera = 1 := by
  ext signal channel
  simp [Module.End.mul_apply]

/-- Reflection preserves the Euclidean inner product exactly. -/
theorem cameraResidueReflectionOperator_inner
    (camera : CameraIndex) (first second : CameraResidueSignal camera) :
    inner ℝ (cameraResidueReflectionOperator camera first)
        (cameraResidueReflectionOperator camera second) =
      inner ℝ first second := by
  simp only [PiLp.inner_apply, Real.inner_apply,
    cameraResidueReflectionOperator_apply]
  simpa [cameraResidueReflection] using
    (cameraResidueReflection (cameraLabel camera)).toEquiv.sum_comp
      (fun channel ↦ first channel * second channel)

/-- The reflection pullback is symmetric; in this finite Hilbert space this
is the exact self-adjointness identity. -/
theorem cameraResidueReflectionOperator_isSymmetric (camera : CameraIndex) :
    (cameraResidueReflectionOperator camera).IsSymmetric := by
  intro first second
  have hinner := cameraResidueReflectionOperator_inner camera first
    (cameraResidueReflectionOperator camera second)
  rw [cameraResidueReflectionOperator_involutive camera second] at hinner
  exact hinner

/-- Projection onto signals even under channel reflection. -/
def cameraResidueEvenProjector (camera : CameraIndex) :
    CameraResidueSignal camera →ₗ[ℝ] CameraResidueSignal camera :=
  ((2 : ℝ)⁻¹) •
    (LinearMap.id + cameraResidueReflectionOperator camera)

/-- Projection onto signals odd under channel reflection. -/
def cameraResidueOddProjector (camera : CameraIndex) :
    CameraResidueSignal camera →ₗ[ℝ] CameraResidueSignal camera :=
  ((2 : ℝ)⁻¹) •
    (LinearMap.id - cameraResidueReflectionOperator camera)

@[simp] theorem cameraResidueEvenProjector_apply
    (camera : CameraIndex) (signal : CameraResidueSignal camera)
    (channel : ZMod (cameraSlope (cameraLabel camera))) :
    cameraResidueEvenProjector camera signal channel =
      (signal channel + signal (-channel)) / 2 := by
  simp [cameraResidueEvenProjector, div_eq_mul_inv]
  ring

@[simp] theorem cameraResidueOddProjector_apply
    (camera : CameraIndex) (signal : CameraResidueSignal camera)
    (channel : ZMod (cameraSlope (cameraLabel camera))) :
    cameraResidueOddProjector camera signal channel =
      (signal channel - signal (-channel)) / 2 := by
  simp [cameraResidueOddProjector, div_eq_mul_inv]
  ring

/-- The even projector lands in the `+1` reflection sector. -/
theorem cameraResidueReflectionOperator_even
    (camera : CameraIndex) (signal : CameraResidueSignal camera) :
    cameraResidueReflectionOperator camera
        (cameraResidueEvenProjector camera signal) =
      cameraResidueEvenProjector camera signal := by
  ext channel
  simp [add_comm]

/-- The odd projector lands in the `-1` reflection sector. -/
theorem cameraResidueReflectionOperator_odd
    (camera : CameraIndex) (signal : CameraResidueSignal camera) :
    cameraResidueReflectionOperator camera
        (cameraResidueOddProjector camera signal) =
      -cameraResidueOddProjector camera signal := by
  ext channel
  simp
  ring

/-- Every signal is the sum of its even and odd parts. -/
theorem cameraResidueEven_add_odd
    (camera : CameraIndex) (signal : CameraResidueSignal camera) :
    cameraResidueEvenProjector camera signal +
        cameraResidueOddProjector camera signal = signal := by
  ext channel
  simp
  ring

/-- The even projection is idempotent. -/
theorem cameraResidueEvenProjector_idempotent
    (camera : CameraIndex) (signal : CameraResidueSignal camera) :
    cameraResidueEvenProjector camera
        (cameraResidueEvenProjector camera signal) =
      cameraResidueEvenProjector camera signal := by
  ext channel
  simp
  ring

/-- The odd projection is idempotent. -/
theorem cameraResidueOddProjector_idempotent
    (camera : CameraIndex) (signal : CameraResidueSignal camera) :
    cameraResidueOddProjector camera
        (cameraResidueOddProjector camera signal) =
      cameraResidueOddProjector camera signal := by
  ext channel
  simp
  ring

/-- The even projector is symmetric. -/
theorem cameraResidueEvenProjector_isSymmetric (camera : CameraIndex) :
    (cameraResidueEvenProjector camera).IsSymmetric := by
  exact (LinearMap.IsSymmetric.id.add
    (cameraResidueReflectionOperator_isSymmetric camera)).smul (by simp)

/-- The odd projector is symmetric. -/
theorem cameraResidueOddProjector_isSymmetric (camera : CameraIndex) :
    (cameraResidueOddProjector camera).IsSymmetric := by
  exact (LinearMap.IsSymmetric.id.sub
    (cameraResidueReflectionOperator_isSymmetric camera)).smul (by simp)

/-- The even projector is a symmetric projection. -/
theorem cameraResidueEvenProjector_isSymmetricProjection
    (camera : CameraIndex) :
    (cameraResidueEvenProjector camera).IsSymmetricProjection where
  isIdempotentElem := by
    apply LinearMap.ext
    exact cameraResidueEvenProjector_idempotent camera
  isSymmetric := cameraResidueEvenProjector_isSymmetric camera

/-- The odd projector is a symmetric projection. -/
theorem cameraResidueOddProjector_isSymmetricProjection
    (camera : CameraIndex) :
    (cameraResidueOddProjector camera).IsSymmetricProjection where
  isIdempotentElem := by
    apply LinearMap.ext
    exact cameraResidueOddProjector_idempotent camera
  isSymmetric := cameraResidueOddProjector_isSymmetric camera

/-- Even and odd residue sectors are orthogonal. -/
theorem inner_cameraResidueEvenProjector_cameraResidueOddProjector
    (camera : CameraIndex) (first second : CameraResidueSignal camera) :
    inner ℝ (cameraResidueEvenProjector camera first)
        (cameraResidueOddProjector camera second) = 0 := by
  let even := cameraResidueEvenProjector camera first
  let odd := cameraResidueOddProjector camera second
  have hreflection := cameraResidueReflectionOperator_isSymmetric camera
    even odd
  have heven : cameraResidueReflectionOperator camera even = even :=
    cameraResidueReflectionOperator_even camera first
  have hodd : cameraResidueReflectionOperator camera odd = -odd :=
    cameraResidueReflectionOperator_odd camera second
  rw [heven, hodd, inner_neg_right] at hreflection
  linarith

/-! ## Literal center/leg signals -/

/-- Unit impulse at one cyclic camera channel. -/
def cameraResidueDelta (camera : CameraIndex)
    (channel : ZMod (cameraSlope (cameraLabel camera))) :
    CameraResidueSignal camera :=
  EuclideanSpace.single channel 1

@[simp] theorem cameraResidueDelta_apply
    (camera : CameraIndex)
    (channel probe : ZMod (cameraSlope (cameraLabel camera))) :
    cameraResidueDelta camera channel probe =
      if probe = channel then 1 else 0 := by
  simp [cameraResidueDelta]

/-- Reflection transports a channel impulse to the impulse on the reflected
channel. -/
theorem cameraResidueReflectionOperator_delta
    (camera : CameraIndex)
    (channel : ZMod (cameraSlope (cameraLabel camera))) :
    cameraResidueReflectionOperator camera
        (cameraResidueDelta camera channel) =
      cameraResidueDelta camera (-channel) := by
  ext probe
  simp [cameraResidueDelta, neg_eq_iff_eq_neg]

/-- The normalized centered-bracket incidence on the cyclic channel space:
the two legs have coefficient `+1` and the fixed center has coefficient
`-2`.  This is the residue-level form of the incidence used by the native
operator scripts and the BR2 independence theorem. -/
def cameraBracketResidueSignal
    (camera : CameraIndex) (radius : ℕ) : CameraResidueSignal camera :=
  cameraResidueDelta camera
      (radius : ZMod (cameraSlope (cameraLabel camera))) +
    cameraResidueDelta camera
      (-(radius : ZMod (cameraSlope (cameraLabel camera)))) -
    (2 : ℝ) • cameraResidueDelta camera 0

/-- Oriented difference of the two leg channels. -/
def cameraOrientedLegResidueSignal
    (camera : CameraIndex) (radius : ℕ) : CameraResidueSignal camera :=
  cameraResidueDelta camera
      (radius : ZMod (cameraSlope (cameraLabel camera))) -
    cameraResidueDelta camera
      (-(radius : ZMod (cameraSlope (cameraLabel camera))))

/-- The centered bracket is fixed by residue reflection. -/
theorem cameraResidueReflectionOperator_bracket
    (camera : CameraIndex) (radius : ℕ) :
    cameraResidueReflectionOperator camera
        (cameraBracketResidueSignal camera radius) =
      cameraBracketResidueSignal camera radius := by
  simp only [cameraBracketResidueSignal, map_sub, map_add, map_smul,
    cameraResidueReflectionOperator_delta, neg_neg, neg_zero]
  abel

/-- The oriented leg difference changes sign under residue reflection. -/
theorem cameraResidueReflectionOperator_orientedLeg
    (camera : CameraIndex) (radius : ℕ) :
    cameraResidueReflectionOperator camera
        (cameraOrientedLegResidueSignal camera radius) =
      -cameraOrientedLegResidueSignal camera radius := by
  simp only [cameraOrientedLegResidueSignal, map_sub,
    cameraResidueReflectionOperator_delta, neg_neg]
  abel

/-- The actual native bracket lies entirely in the even residue sector. -/
theorem cameraResidueEvenProjector_bracket
    (camera : CameraIndex) (radius : ℕ) :
    cameraResidueEvenProjector camera
        (cameraBracketResidueSignal camera radius) =
      cameraBracketResidueSignal camera radius := by
  ext channel
  have hfixed := congrArg
    (fun signal : CameraResidueSignal camera ↦ signal channel)
    (cameraResidueReflectionOperator_bracket camera radius)
  simp only [cameraResidueReflectionOperator_apply] at hfixed
  simp [hfixed]

/-- Consequently the odd projector kills the centered bracket exactly. -/
theorem cameraResidueOddProjector_bracket
    (camera : CameraIndex) (radius : ℕ) :
    cameraResidueOddProjector camera
        (cameraBracketResidueSignal camera radius) = 0 := by
  ext channel
  have hfixed := congrArg
    (fun signal : CameraResidueSignal camera ↦ signal channel)
    (cameraResidueReflectionOperator_bracket camera radius)
  simp only [cameraResidueReflectionOperator_apply] at hfixed
  simp [hfixed]

/-- The oriented leg signal lies entirely in the odd residue sector. -/
theorem cameraResidueOddProjector_orientedLeg
    (camera : CameraIndex) (radius : ℕ) :
    cameraResidueOddProjector camera
        (cameraOrientedLegResidueSignal camera radius) =
      cameraOrientedLegResidueSignal camera radius := by
  ext channel
  have hanti := congrArg
    (fun signal : CameraResidueSignal camera ↦ signal channel)
    (cameraResidueReflectionOperator_orientedLeg camera radius)
  simp only [cameraResidueReflectionOperator_apply] at hanti
  simp [hanti]

/-- Consequently the even projector kills the oriented leg difference. -/
theorem cameraResidueEvenProjector_orientedLeg
    (camera : CameraIndex) (radius : ℕ) :
    cameraResidueEvenProjector camera
        (cameraOrientedLegResidueSignal camera radius) = 0 := by
  ext channel
  have hanti := congrArg
    (fun signal : CameraResidueSignal camera ↦ signal channel)
    (cameraResidueReflectionOperator_orientedLeg camera radius)
  simp only [cameraResidueReflectionOperator_apply] at hanti
  simp [hanti]

/-- At the antipodal emitted radius the two legs are the same channel, so the
oriented odd signal vanishes exactly. -/
theorem cameraOrientedLegResidueSignal_eq_zero_of_antipodal
    (camera : CameraIndex) {radius : ℕ}
    (hradius : radius ∈ radiusSet (cameraLabel camera))
    (hantipodal : 2 * radius = cameraSlope (cameraLabel camera)) :
    cameraOrientedLegResidueSignal camera radius = 0 := by
  have hfixed :=
    (cameraResidueReflection_radius_fixed_iff_antipodal
      (camera := cameraLabel camera) (radius := radius)
      camera.property hradius).2 hantipodal
  change -(radius : ZMod (cameraSlope (cameraLabel camera))) = radius at hfixed
  simp [cameraOrientedLegResidueSignal, hfixed]

end

end CarrySelfAdjointOperator

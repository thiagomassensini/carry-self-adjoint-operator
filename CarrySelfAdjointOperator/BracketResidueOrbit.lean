import CarrySelfAdjointOperator.BracketLegLatticeSeparation
import Mathlib.Data.ZMod.Basic

/-!
# Native bracket channels as reflection orbits in `ZMod`

The exact natural-number residue ledger is packaged here in the finite cyclic
group belonging to each camera slope.  The center is the zero channel.  The
right and left legs are the channels `r` and `-r`, exchanged by the canonical
reflection.  Their orbit is disjoint from the center sector, and it collapses
to one channel exactly at the antipodal radius `2r = d`.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera

/-- The three cyclic channels occupied by one aligned bracket of a camera. -/
structure BracketResidueChannels (camera : ℕ) where
  center : ZMod (cameraSlope camera)
  left : ZMod (cameraSlope camera)
  right : ZMod (cameraSlope camera)
deriving DecidableEq

@[ext] theorem BracketResidueChannels.ext
    {camera : ℕ} {x y : BracketResidueChannels camera}
    (hcenter : x.center = y.center) (hleft : x.left = y.left)
    (hright : x.right = y.right) : x = y := by
  cases x
  cases y
  simp_all

/-- The literal center and leg indices transported to the cyclic camera
quotient. -/
def alignedBracketResidueChannels
    (camera index radius : ℕ) : BracketResidueChannels camera where
  center := ((alignedCenter camera index : ℕ) :
    ZMod (cameraSlope camera))
  left := ((alignedCenter camera index - radius : ℕ) :
    ZMod (cameraSlope camera))
  right := ((alignedCenter camera index + radius : ℕ) :
    ZMod (cameraSlope camera))

/-- Canonical reflection of a cyclic camera channel. -/
def cameraResidueReflection (camera : ℕ) :
    ZMod (cameraSlope camera) ≃+ ZMod (cameraSlope camera) :=
  AddEquiv.neg _

@[simp] theorem cameraResidueReflection_apply
    (camera : ℕ) (channel : ZMod (cameraSlope camera)) :
    cameraResidueReflection camera channel = -channel := rfl

/-- Reflection is an involution on every camera quotient. -/
theorem cameraResidueReflection_involutive (camera : ℕ) :
    Function.Involutive (cameraResidueReflection camera) := by
  intro channel
  simp

/-- The abstract fixed points of camera reflection are zero and, when it
exists, the order-two channel represented by half the slope. -/
theorem cameraResidueReflection_fixed_iff
    (camera : ℕ) (channel : ZMod (cameraSlope camera)) :
    cameraResidueReflection camera channel = channel ↔
      channel = 0 ∨ 2 * channel.val = cameraSlope camera := by
  simpa [cameraResidueReflection] using ZMod.neg_eq_self_iff channel

/-- The literal aligned center becomes the zero cyclic channel. -/
@[simp] theorem alignedBracketResidueChannels_center_eq_zero
    (camera index radius : ℕ) :
    (alignedBracketResidueChannels camera index radius).center = 0 := by
  simp [alignedBracketResidueChannels, alignedCenter_eq_cameraSlope_mul]

/-- The right leg becomes the positive-radius channel. -/
theorem alignedBracketResidueChannels_right_eq_radius
    {camera index radius : ℕ} :
    (alignedBracketResidueChannels camera index radius).right =
      (radius : ZMod (cameraSlope camera)) := by
  simp [alignedBracketResidueChannels, alignedCenter_eq_cameraSlope_mul]

/-- The left leg becomes the reflected radius channel. -/
theorem alignedBracketResidueChannels_left_eq_neg_radius
    {camera index radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    (alignedBracketResidueChannels camera index radius).left =
      -(radius : ZMod (cameraSlope camera)) := by
  have hradiusBounds := emittedRadius_pos_and_lt_cameraSlope hcamera hradius
  have hleftMod :=
    leftBracketLeg_mod_cameraSlope_eq_slope_sub_radius
      (index := index) hcamera hradius
  have hsubLt : cameraSlope camera - radius < cameraSlope camera := by
    omega
  have hcast :
      ((alignedCenter camera index - radius : ℕ) :
          ZMod (cameraSlope camera)) =
        (cameraSlope camera - radius : ℕ) := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).2
    rw [hleftMod, Nat.mod_eq_of_lt hsubLt]
  rw [alignedBracketResidueChannels, hcast]
  rw [Nat.cast_sub (by omega : radius ≤ cameraSlope camera)]
  simp

/-- Complete normalization of the cyclic bracket ledger. -/
theorem alignedBracketResidueChannels_eq_normalForm
    {camera index radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    alignedBracketResidueChannels camera index radius =
      { center := 0
        left := -(radius : ZMod (cameraSlope camera))
        right := (radius : ZMod (cameraSlope camera)) } := by
  apply BracketResidueChannels.ext
  · exact alignedBracketResidueChannels_center_eq_zero camera index radius
  · exact alignedBracketResidueChannels_left_eq_neg_radius hcamera hradius
  · exact alignedBracketResidueChannels_right_eq_radius

/-- The two leg channels are exchanged by camera reflection. -/
theorem cameraResidueReflection_right_eq_left
    {camera index radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    cameraResidueReflection camera
        (alignedBracketResidueChannels camera index radius).right =
      (alignedBracketResidueChannels camera index radius).left := by
  rw [cameraResidueReflection_apply,
    alignedBracketResidueChannels_right_eq_radius,
    alignedBracketResidueChannels_left_eq_neg_radius hcamera hradius]

/-- Reflection also sends the left leg back to the right leg. -/
theorem cameraResidueReflection_left_eq_right
    {camera index radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    cameraResidueReflection camera
        (alignedBracketResidueChannels camera index radius).left =
      (alignedBracketResidueChannels camera index radius).right := by
  rw [cameraResidueReflection_apply,
    alignedBracketResidueChannels_left_eq_neg_radius hcamera hradius,
    alignedBracketResidueChannels_right_eq_radius]
  simp

/-- The zero center channel is fixed by cyclic reflection. -/
theorem cameraResidueReflection_center_eq_center
    (camera index radius : ℕ) :
    cameraResidueReflection camera
        (alignedBracketResidueChannels camera index radius).center =
      (alignedBracketResidueChannels camera index radius).center := by
  rw [alignedBracketResidueChannels_center_eq_zero]
  simp

/-- The center sector is the singleton fixed channel zero. -/
def centerResidueSector (camera : ℕ) :
    Finset (ZMod (cameraSlope camera)) :=
  {0}

/-- The leg sector is exactly the reflection orbit of the radius channel. -/
def legResidueOrbit (camera radius : ℕ) :
    Finset (ZMod (cameraSlope camera)) :=
  {(radius : ZMod (cameraSlope camera)),
    -(radius : ZMod (cameraSlope camera))}

/-- Membership in the leg sector is invariant under cyclic reflection. -/
theorem cameraResidueReflection_mem_legResidueOrbit_iff
    {camera radius : ℕ} (channel : ZMod (cameraSlope camera)) :
    cameraResidueReflection camera channel ∈ legResidueOrbit camera radius ↔
      channel ∈ legResidueOrbit camera radius := by
  simp [cameraResidueReflection, legResidueOrbit, or_comm,
    neg_eq_iff_eq_neg]

/-- A supported emitted bracket has a leg orbit disjoint from its center
sector. -/
theorem centerResidueSector_disjoint_legResidueOrbit
    {camera radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    Disjoint (centerResidueSector camera) (legResidueOrbit camera radius) := by
  have hnonzero :
      (radius : ZMod (cameraSlope camera)) ≠ 0 := by
    intro hzero
    apply cameraSlope_not_dvd_emittedRadius hcamera hradius
    exact (ZMod.natCast_eq_zero_iff radius (cameraSlope camera)).mp hzero
  simp [centerResidueSector, legResidueOrbit, hnonzero, hnonzero.symm]

/-- Both literal legs lie in the canonical leg reflection orbit. -/
theorem alignedBracketResidueChannels_legs_mem_orbit
    {camera index radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    (alignedBracketResidueChannels camera index radius).left ∈
        legResidueOrbit camera radius ∧
      (alignedBracketResidueChannels camera index radius).right ∈
        legResidueOrbit camera radius := by
  rw [alignedBracketResidueChannels_left_eq_neg_radius hcamera hradius,
    alignedBracketResidueChannels_right_eq_radius]
  simp [legResidueOrbit]

/-- The abstract reflection orbit is literally the unordered pair of emitted
leg channels. -/
theorem alignedBracketResidueChannels_legPair_eq_orbit
    {camera index radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    { (alignedBracketResidueChannels camera index radius).left,
        (alignedBracketResidueChannels camera index radius).right } =
      legResidueOrbit camera radius := by
  rw [alignedBracketResidueChannels_left_eq_neg_radius hcamera hradius,
    alignedBracketResidueChannels_right_eq_radius]
  ext channel
  simp [legResidueOrbit, or_comm]

/-- The radius channel is fixed by reflection exactly at the antipodal
radius.  The zero fixed point is excluded by emitted-radius positivity. -/
theorem cameraResidueReflection_radius_fixed_iff_antipodal
    {camera radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    cameraResidueReflection camera
        (radius : ZMod (cameraSlope camera)) = radius ↔
      2 * radius = cameraSlope camera := by
  have hradiusBounds := emittedRadius_pos_and_lt_cameraSlope hcamera hradius
  have hnonzero :
      (radius : ZMod (cameraSlope camera)) ≠ 0 := by
    intro hzero
    apply cameraSlope_not_dvd_emittedRadius hcamera hradius
    exact (ZMod.natCast_eq_zero_iff radius (cameraSlope camera)).mp hzero
  rw [cameraResidueReflection_fixed_iff]
  simp [hnonzero, ZMod.val_natCast_of_lt hradiusBounds.2]

/-- The leg orbit has two channels exactly away from the antipodal radius. -/
theorem legResidueOrbit_card_eq_two_iff_not_antipodal
    {camera radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    (legResidueOrbit camera radius).card = 2 ↔
      2 * radius ≠ cameraSlope camera := by
  rw [legResidueOrbit, Finset.card_pair_eq_two_iff]
  constructor
  · intro hne hanti
    apply hne
    have hfixed :=
      (cameraResidueReflection_radius_fixed_iff_antipodal hcamera hradius).2 hanti
    simpa [cameraResidueReflection] using hfixed.symm
  · intro hnotAntipodal heq
    apply hnotAntipodal
    apply (cameraResidueReflection_radius_fixed_iff_antipodal hcamera hradius).1
    simpa [cameraResidueReflection] using heq.symm

/-- The leg orbit collapses to one channel exactly at the antipodal radius. -/
theorem legResidueOrbit_card_eq_one_iff_antipodal
    {camera radius : ℕ} (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera) :
    (legResidueOrbit camera radius).card = 1 ↔
      2 * radius = cameraSlope camera := by
  have hcard := Finset.card_pair_eq_one_or_two
    (a := (radius : ZMod (cameraSlope camera)))
    (b := -(radius : ZMod (cameraSlope camera)))
  rw [← legResidueOrbit] at hcard
  have htwo := legResidueOrbit_card_eq_two_iff_not_antipodal hcamera hradius
  omega

end CarrySelfAdjointOperator

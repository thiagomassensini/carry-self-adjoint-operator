import NativeCarrySpectralWeyl.Camera.Geometry
import Mathlib.Tactic

/-!
# All-base center--leg diagonal exclusion

The apparent diagonal of a center/leg kernel is not a geometric diagonal.

For every supported camera base `b >= 2`:

* every aligned center is divisible by `b`;
* every admissible radius satisfies `0 < r < b`;
* therefore the two legs `center - r` and `center + r` are not divisible by
  `b`;
* hence no leg can coincide with any aligned center of the same base.

No primality hypothesis occurs. Odd, even, prime and composite bases are
covered uniformly. The exceptional C2 alignment on multiples of four is also
covered because those centers remain divisible by the camera base two.

This is the arithmetic theorem distinguishing a matrix-index diagonal `i = j`
from equality of the underlying geometric coordinates.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Left leg of the centered bracket emitted by `base` at an aligned center. -/
def cameraLeftLeg (base index radius : ℕ) : ℕ :=
  alignedCenter base index - radius

/-- Right leg of the centered bracket emitted by `base` at an aligned center. -/
def cameraRightLeg (base index radius : ℕ) : ℕ :=
  alignedCenter base index + radius

/-- Every aligned center is divisible by its camera base.

For C2 the actual center period is four, but divisibility by the camera base
two still holds. For every other base the aligned centers are literally its
positive multiples. -/
theorem cameraBase_dvd_alignedCenter (base index : ℕ) :
    base ∣ alignedCenter base index := by
  by_cases h2 : base = 2
  · subst base
    rw [alignedCenter_two]
    refine ⟨2 * (index + 1), ?_⟩
    omega
  · rw [alignedCenter_of_ne_two h2]
    exact ⟨index + 1, rfl⟩

/-- An admissible bracket radius is positive. -/
theorem cameraRadius_pos_of_mem
    {base radius : ℕ} (hradius : radius ∈ radiusSet base) :
    0 < radius := by
  have hrange := (mem_radiusSet_iff).1 hradius
  omega

/-- In every supported base, an admissible radius is strictly smaller than
the base. This uses only `radius <= floor(base / 2)` and `base >= 2`; no
prime-factor property is involved. -/
theorem cameraRadius_lt_base
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    radius < base := by
  change 2 ≤ base at hbase
  have hrange := (mem_radiusSet_iff).1 hradius
  omega

/-- A supported aligned center is positive. -/
theorem alignedCenter_pos_of_supported
    {base : ℕ} (hbase : IsSupported base) (index : ℕ) :
    0 < alignedCenter base index := by
  change 2 ≤ base at hbase
  by_cases h2 : base = 2
  · subst base
    rw [alignedCenter_two]
    positivity
  · rw [alignedCenter_of_ne_two h2]
    exact Nat.mul_pos (by omega) (by omega)

/-- An admissible radius lies strictly before every aligned center of the
same supported base, so natural subtraction in the left leg loses nothing. -/
theorem cameraRadius_lt_alignedCenter
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (index : ℕ) :
    radius < alignedCenter base index := by
  have hrlt : radius < base :=
    cameraRadius_lt_base hbase hradius
  have hbaseDvd : base ∣ alignedCenter base index :=
    cameraBase_dvd_alignedCenter base index
  have hbaseLe : base ≤ alignedCenter base index :=
    Nat.le_of_dvd (alignedCenter_pos_of_supported hbase index) hbaseDvd
  exact lt_of_lt_of_le hrlt hbaseLe

/-- A positive radius strictly below the base cannot be divisible by that
base. -/
theorem cameraBase_not_dvd_radius
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    ¬ base ∣ radius :=
  Nat.not_dvd_of_pos_of_lt
    (cameraRadius_pos_of_mem hradius)
    (cameraRadius_lt_base hbase hradius)

/-- The left leg leaves the center divisibility class. -/
theorem cameraBase_not_dvd_leftLeg
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (index : ℕ) :
    ¬ base ∣ cameraLeftLeg base index radius := by
  intro hleg
  have hcenter : base ∣ alignedCenter base index :=
    cameraBase_dvd_alignedCenter base index
  have hrle : radius ≤ alignedCenter base index :=
    Nat.le_of_lt (cameraRadius_lt_alignedCenter hbase hradius index)
  have hradiusDvd : base ∣ radius :=
    (Nat.dvd_sub_iff_right hrle hcenter).1
      (by simpa [cameraLeftLeg] using hleg)
  exact (cameraBase_not_dvd_radius hbase hradius) hradiusDvd

/-- The right leg leaves the center divisibility class. -/
theorem cameraBase_not_dvd_rightLeg
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (index : ℕ) :
    ¬ base ∣ cameraRightLeg base index radius := by
  intro hleg
  have hcenter : base ∣ alignedCenter base index :=
    cameraBase_dvd_alignedCenter base index
  have hsum : base ∣ radius + alignedCenter base index := by
    simpa [cameraRightLeg, Nat.add_comm] using hleg
  have hradiusDvd : base ∣ radius :=
    ((Nat.dvd_add_iff_left hcenter).symm).1 hsum
  exact (cameraBase_not_dvd_radius hbase hradius) hradiusDvd

/-- No left leg can equal any aligned center of the same base. -/
theorem alignedCenter_ne_cameraLeftLeg
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (centerIndex legIndex : ℕ) :
    alignedCenter base centerIndex ≠
      cameraLeftLeg base legIndex radius := by
  intro heq
  have hlegDvd : base ∣ cameraLeftLeg base legIndex radius := by
    rw [← heq]
    exact cameraBase_dvd_alignedCenter base centerIndex
  exact (cameraBase_not_dvd_leftLeg hbase hradius legIndex) hlegDvd

/-- No right leg can equal any aligned center of the same base. -/
theorem alignedCenter_ne_cameraRightLeg
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (centerIndex legIndex : ℕ) :
    alignedCenter base centerIndex ≠
      cameraRightLeg base legIndex radius := by
  intro heq
  have hlegDvd : base ∣ cameraRightLeg base legIndex radius := by
    rw [← heq]
    exact cameraBase_dvd_alignedCenter base centerIndex
  exact (cameraBase_not_dvd_rightLeg hbase hradius legIndex) hlegDvd

/-- Main all-base diagonal-exclusion theorem.

An aligned center cannot equal either leg of any admissible centered bracket
from the same base. The theorem assumes only support `base >= 2`; in
particular, `Nat.Prime base` is neither required nor mentioned. -/
theorem allBase_centerLeg_diagonal_impossible
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (centerIndex legIndex : ℕ) :
    alignedCenter base centerIndex ≠
        cameraLeftLeg base legIndex radius ∧
      alignedCenter base centerIndex ≠
        cameraRightLeg base legIndex radius :=
  ⟨alignedCenter_ne_cameraLeftLeg
      hbase hradius centerIndex legIndex,
    alignedCenter_ne_cameraRightLeg
      hbase hradius centerIndex legIndex⟩

/-- Even the same matrix index does not produce equality of geometric
coordinates: `(center_i, leftLeg_i)` is off the coordinate diagonal. -/
theorem sameIndex_center_leftLeg_offDiagonal
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (index : ℕ) :
    alignedCenter base index ≠ cameraLeftLeg base index radius :=
  alignedCenter_ne_cameraLeftLeg hbase hradius index index

/-- Same-index center/right-leg evaluations are also geometrically
off-diagonal. -/
theorem sameIndex_center_rightLeg_offDiagonal
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (index : ℕ) :
    alignedCenter base index ≠ cameraRightLeg base index radius :=
  alignedCenter_ne_cameraRightLeg hbase hradius index index

/-- Predicate for the center lattice of one camera. -/
def IsCameraAlignedCenter (base n : ℕ) : Prop :=
  ∃ index : ℕ, n = alignedCenter base index

/-- Predicate for either leg of an admissible centered bracket of one
camera. -/
def IsCameraBracketLeg (base n : ℕ) : Prop :=
  ∃ index radius : ℕ,
    radius ∈ radiusSet base ∧
      (n = cameraLeftLeg base index radius ∨
        n = cameraRightLeg base index radius)

/-- Every point in the center lattice is divisible by the base. -/
theorem cameraBase_dvd_of_isCameraAlignedCenter
    {base n : ℕ} (hcenter : IsCameraAlignedCenter base n) :
    base ∣ n := by
  rcases hcenter with ⟨index, rfl⟩
  exact cameraBase_dvd_alignedCenter base index

/-- No admissible bracket leg is divisible by the base. -/
theorem cameraBase_not_dvd_of_isCameraBracketLeg
    {base n : ℕ}
    (hbase : IsSupported base)
    (hleg : IsCameraBracketLeg base n) :
    ¬ base ∣ n := by
  intro hnDvd
  rcases hleg with ⟨index, radius, hradius, hleft | hright⟩
  · subst n
    exact (cameraBase_not_dvd_leftLeg hbase hradius index) hnDvd
  · subst n
    exact (cameraBase_not_dvd_rightLeg hbase hradius index) hnDvd

/-- Set-level form: the center role and leg role of one supported base are
disjoint. -/
theorem no_point_is_both_cameraCenter_and_cameraLeg
    {base n : ℕ}
    (hbase : IsSupported base) :
    ¬ (IsCameraAlignedCenter base n ∧ IsCameraBracketLeg base n) := by
  rintro ⟨hcenter, hleg⟩
  exact
    (cameraBase_not_dvd_of_isCameraBracketLeg hbase hleg)
      (cameraBase_dvd_of_isCameraAlignedCenter hcenter)

/-- There is no geometric center--leg diagonal in any supported camera. -/
def HasCameraCenterLegDiagonal (base : ℕ) : Prop :=
  ∃ n : ℕ,
    IsCameraAlignedCenter base n ∧ IsCameraBracketLeg base n

/-- Global impossibility of the center--leg diagonal for every supported
base, prime or composite. -/
theorem not_hasCameraCenterLegDiagonal
    {base : ℕ} (hbase : IsSupported base) :
    ¬ HasCameraCenterLegDiagonal base := by
  rintro ⟨n, hcenter, hleg⟩
  exact no_point_is_both_cameraCenter_and_cameraLeg
    hbase ⟨hcenter, hleg⟩

/-- Uniform all-bases capstone. -/
theorem allSupportedBases_centerLegDiagonalImpossible :
    ∀ base : ℕ,
      IsSupported base →
        ¬ HasCameraCenterLegDiagonal base :=
  fun _ hbase => not_hasCameraCenterLegDiagonal hbase

end

end CarrySelfAdjointOperator

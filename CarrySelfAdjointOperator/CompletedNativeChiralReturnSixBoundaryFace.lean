import CarrySelfAdjointOperator.CompletedNativeChiralReturnEleventhSourceJet
import CarrySelfAdjointOperator.CompletedNativeChiralReturnTenthSourceIntegral

/-!
# Exact six-coordinate Green boundary face

The certified even three-coordinate face is retained. The new odd face
is determined by the eleventh source jet and the existing alternating
Green tower. All crosses remain. One raw-integral sign is isolated;
no positivity of this new face or of full N=6 storage is assumed.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The new odd block retains all three pairwise crosses. -/
def nativeSourceSixOddBoundaryEnergy (u v w : ℂ) : ℝ :=
  nativeSourceOddBoundaryCoefficient 1 * Complex.normSq u -
    2 * nativeSourceOddBoundaryCoefficient 2 * (conj u*v).re +
    2 * nativeSourceOddBoundaryCoefficient 3 * (conj u*w).re +
    nativeSourceOddBoundaryCoefficient 3 * Complex.normSq v -
    2 * nativeSourceOddBoundaryCoefficient 4 * (conj v*w).re +
    nativeSourceOddBoundaryCoefficient 5 * Complex.normSq w

/-- The coefficient forced by elimination of the first two odd boundary
coordinates. Defined from the original source derivatives, not a target Gram. -/
def nativeSourceSixOddDiscriminant : ℝ :=
  nativeSourceOddBoundaryCoefficient 1 * nativeSourceOddBoundaryCoefficient 3 *
      nativeSourceOddBoundaryCoefficient 5 +
    2 * nativeSourceOddBoundaryCoefficient 2 * nativeSourceOddBoundaryCoefficient 3 *
      nativeSourceOddBoundaryCoefficient 4 -
    nativeSourceOddBoundaryCoefficient 1 * nativeSourceOddBoundaryCoefficient 4^2 -
    nativeSourceOddBoundaryCoefficient 2^2 * nativeSourceOddBoundaryCoefficient 5 -
    nativeSourceOddBoundaryCoefficient 3^3

/-- Raw-integral polynomial fixed by the source recurrence and the mixed
Green boundary identity. This is an algebraic obstruction scalar, not a
new carrier, metric, operator or positivity assumption. -/
def nativeSourceTwelfthMixedNumerator (a b c d e f g : ℝ) : ℝ :=
  -1260*a^3*c*e*g +
    1925*a^3*c*f^2 +
    2646*a^3*d^2*g -
    13860*a^3*d*e*f +
    11880*a^3*e^3 +
    3780*a^2*b^2*e*g -
    5775*a^2*b^2*f^2 -
    44100*a^2*b*c*d*g +
    117810*a^2*b*c*e*f +
    213444*a^2*b*d^2*f -
    374220*a^2*b*d*e^2 +
    44100*a^2*c^3*g -
    323400*a^2*c^2*d*f -
    623700*a^2*c^2*e^2 +
    2182950*a^2*c*d^2*e -
    1222452*a^2*d^4 +
    52920*a*b^3*d*g -
    145530*a*b^3*e*f -
    66150*a*b^2*c^2*g -
    1455300*a*b^2*c*d*f +
    3898125*a*b^2*c*e^2 -
    873180*a*b^2*d^2*e +
    1940400*a*b*c^3*f -
    16008300*a*b*c^2*d*e +
    12224520*a*b*c*d^3 +
    7276500*a*c^4*e -
    6791400*a*c^3*d^2 +
    2328480*b^4*d*f -
    4209975*b^4*e^2 -
    2910600*b^3*c^2*f +
    21829500*b^3*c*d*e -
    16299360*b^3*d^3 -
    10914750*b^2*c^3*e +
    10187100*b^2*c^2*d^2

/-- All factors, factorials and signs are certified directly from raw jets. -/
theorem nativeSourceSixOddDiscriminant_integral_formula :
    nativeSourceSixOddDiscriminant =
      nativeSourceTwelfthMixedNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) /
        (1520925880320000 * completedNativeXiCosineMoment 0 ^ 6) := by
  obtain ⟨_, h1, h2, h3⟩ := nativeSourceOddBoundaryCoefficient_integral_formulas
  unfold nativeSourceSixOddDiscriminant
  rw [h1, h2, h3, nativeSourceOddBoundaryCoefficient_four_integral_formula,
    nativeSourceOddBoundaryCoefficient_five_integral_formula]
  unfold nativeSourceTwelfthMixedNumerator nativeSourceSeventhNumerator nativeSourceNinthNumerator nativeSourceEleventhNumerator
  field_simp [(completedNativeXiCosineMoment_pos 0).ne']
  ring

/-- The new sign is exactly a raw integral inequality, with positive divisor. -/
theorem nativeSourceSixOddDiscriminant_pos_iff_rawIntegral :
    0 < nativeSourceSixOddDiscriminant ↔
      0 < nativeSourceTwelfthMixedNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) := by
  rw [nativeSourceSixOddDiscriminant_integral_formula]
  exact div_pos_iff_of_pos_right (by positivity [completedNativeXiCosineMoment_pos 0])

/-- Exact square completion in the EXISTING complex norm, retaining crosses.
No square root, whitening, target matrix or change of metric is involved. -/
theorem nativeSourceSixOddBoundaryEnergy_square (u v w : ℂ) :
    let a := nativeSourceOddBoundaryCoefficient 1
    let b := nativeSourceOddBoundaryCoefficient 2
    let c := nativeSourceOddBoundaryCoefficient 3
    let d := nativeSourceOddBoundaryCoefficient 4
    let δ := a*c-b^2
    nativeSourceSixOddBoundaryEnergy u v w =
      a * Complex.normSq (u - ((b/a : ℝ) : ℂ)*v + ((c/a : ℝ) : ℂ)*w) +
      (δ/a) * Complex.normSq (v + (((b*c-a*d)/δ : ℝ) : ℂ)*w) +
      (nativeSourceSixOddDiscriminant/δ) * Complex.normSq w := by
  dsimp only
  have ha := nativeSourceMixedLeadingCoefficients_pos.2.ne'
  have hd := nativeSourceMixedDiscriminants_pos.2.ne'
  unfold nativeSourceSixOddBoundaryEnergy nativeSourceSixOddDiscriminant
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, add_zero, sub_zero]
  field_simp [ha, hd]
  ring

/-- Strict positivity of this new odd FACE is equivalent to precisely one
new source sign. This equivalence neither assumes nor closes that sign. -/
theorem nativeSourceSixOddBoundaryEnergy_pos_iff :
    (∀ u v w : ℂ, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) →
      0 < nativeSourceSixOddBoundaryEnergy u v w) ↔
      0 < nativeSourceSixOddDiscriminant := by
  let a := nativeSourceOddBoundaryCoefficient 1
  let b := nativeSourceOddBoundaryCoefficient 2
  let c := nativeSourceOddBoundaryCoefficient 3
  let d := nativeSourceOddBoundaryCoefficient 4
  let δ := a*c-b^2
  have ha : 0 < a := nativeSourceMixedLeadingCoefficients_pos.2
  have hd : 0 < δ := nativeSourceMixedDiscriminants_pos.2
  constructor
  · intro hp
    let v : ℂ := (-((b*c-a*d)/δ : ℝ) : ℂ)
    let u : ℂ := ((b/a : ℝ) : ℂ)*v - ((c/a : ℝ) : ℂ)
    have ht := hp u v 1 (Or.inr (Or.inr one_ne_zero))
    rw [nativeSourceSixOddBoundaryEnergy_square] at ht
    change 0 < a * Complex.normSq (u - ((b/a : ℝ) : ℂ)*v + ((c/a : ℝ) : ℂ)*1) +
      (δ/a) * Complex.normSq (v + (((b*c-a*d)/δ : ℝ) : ℂ)*1) +
      (nativeSourceSixOddDiscriminant/δ) * Complex.normSq (1 : ℂ) at ht
    have hfirst : u - ((b/a : ℝ) : ℂ)*v + ((c/a : ℝ) : ℂ) = 0 := by
      dsimp only [u]
      ring
    have hsecond : v + (((b*c-a*d)/δ : ℝ) : ℂ) = 0 := by
      dsimp only [v]
      push_cast
      ring
    simp only [mul_one, hfirst, hsecond, Complex.normSq_zero, mul_zero,
      zero_add, Complex.normSq_one] at ht
    exact (div_pos_iff_of_pos_right hd).mp ht
  · intro hnew u v w hnonzero
    rw [nativeSourceSixOddBoundaryEnergy_square]
    change 0 < a * Complex.normSq (u - ((b/a : ℝ) : ℂ)*v + ((c/a : ℝ) : ℂ)*w) +
      (δ/a) * Complex.normSq (v + (((b*c-a*d)/δ : ℝ) : ℂ)*w) +
      (nativeSourceSixOddDiscriminant/δ) * Complex.normSq w
    by_cases hw : w = 0
    · rw [hw]
      simp only [mul_zero, add_zero, Complex.normSq_zero]
      have huv : u ≠ 0 ∨ v ≠ 0 := by tauto
      by_cases hv : v = 0
      · have hu : u ≠ 0 := huv.resolve_right (not_ne_iff.mpr hv)
        simpa [hv] using mul_pos ha (Complex.normSq_pos.mpr hu)
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg ha.le (Complex.normSq_nonneg _))
          (mul_pos (div_pos hd ha) (Complex.normSq_pos.mpr hv))
    · exact add_pos_of_nonneg_of_pos
        (add_nonneg (mul_nonneg ha.le (Complex.normSq_nonneg _))
          (mul_nonneg (div_pos hd ha).le (Complex.normSq_nonneg _)))
        (mul_pos (div_pos hnew hd) (Complex.normSq_pos.mpr hw))

/-- The SIX-coordinate boundary face retains both three-coordinate sectors. -/
def nativeSourceSixBoundaryEnergy (x : Fin 6 → ℂ) : ℝ :=
  2 * (nativeSourceFiveEvenBoundaryEnergy (x 0) (x 2) (x 4) +
    nativeSourceSixOddBoundaryEnergy (x 1) (x 3) (x 5))

/-- The already-certified even sector leaves exactly one new odd source sign. -/
theorem nativeSourceSixBoundaryEnergy_pos_iff :
    (∀ x : Fin 6 → ℂ, x ≠ 0 → 0 < nativeSourceSixBoundaryEnergy x) ↔
      0 < nativeSourceSixOddDiscriminant := by
  constructor
  · intro h
    apply nativeSourceSixOddBoundaryEnergy_pos_iff.mp
    intro u v w hn
    let x : Fin 6 → ℂ := ![0, u, 0, v, 0, w]
    have hx : x ≠ 0 := by
      intro hz
      have h1 := congrFun hz 1
      have h3 := congrFun hz 3
      have h5 := congrFun hz 5
      simp [x] at h1 h3 h5
      tauto
    have ht := h x hx
    change 0 < 2 * (nativeSourceFiveEvenBoundaryEnergy 0 0 0 +
      nativeSourceSixOddBoundaryEnergy u v w) at ht
    simp only [nativeSourceFiveEvenBoundaryEnergy, map_zero, mul_zero,
      Complex.zero_re, sub_zero, add_zero, zero_add] at ht
    linarith
  · intro hn x hx
    have hp := nativeSourceSixOddBoundaryEnergy_pos_iff.mpr hn
    have he : 0 ≤ nativeSourceFiveEvenBoundaryEnergy (x 0) (x 2) (x 4) := by
      by_cases h : x 0 ≠ 0 ∨ x 2 ≠ 0 ∨ x 4 ≠ 0
      · exact (nativeSourceFiveEvenBoundaryEnergy_pos _ _ _ h).le
      · simp only [not_or, not_ne_iff] at h
        simp [nativeSourceFiveEvenBoundaryEnergy, h.1, h.2.1, h.2.2]
    have ho : 0 ≤ nativeSourceSixOddBoundaryEnergy (x 1) (x 3) (x 5) := by
      by_cases h : x 1 ≠ 0 ∨ x 3 ≠ 0 ∨ x 5 ≠ 0
      · exact (hp _ _ _ h).le
      · simp only [not_or, not_ne_iff] at h
        simp [nativeSourceSixOddBoundaryEnergy, h.1, h.2.1, h.2.2]
    have hnonzero : (x 0 ≠ 0 ∨ x 2 ≠ 0 ∨ x 4 ≠ 0) ∨
        (x 1 ≠ 0 ∨ x 3 ≠ 0 ∨ x 5 ≠ 0) := by
      by_contra h
      simp only [not_or, not_ne_iff] at h
      apply hx
      funext i
      fin_cases i <;> simp [h]
    unfold nativeSourceSixBoundaryEnergy
    rcases hnonzero with hn | hn
    · exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
        (nativeSourceFiveEvenBoundaryEnergy_pos _ _ _ hn) ho)
    · exact mul_pos (by norm_num) (add_pos_of_nonneg_of_pos he (hp _ _ _ hn))

/-- Zero extension is only the limiting face; no finite-step source jet is deleted. -/
def nativeSourceSixBoundaryExtension (x : Fin 6 → ℂ) (m : ℕ) : ℂ :=
  if h : m < 6 then x ⟨m, h⟩ else 0

/-- Both parity blocks come exactly from the existing polarized Green tower. -/
theorem nativeSourceSixBoundaryEnergy_eq_alternating_green (x : Fin 6 → ℂ) :
    nativeSourceSixBoundaryEnergy x =
      2 * ∑ j ∈ Finset.range 6, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
        (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
          (conj (nativeSourceSixBoundaryExtension x a) *
            nativeSourceSixBoundaryExtension x (2*j-a)).re) := by
  norm_num [Finset.sum_range_succ, nativeSourceSixBoundaryExtension,
    nativeSourceSixBoundaryEnergy, nativeSourceFiveEvenBoundaryEnergy,
    nativeSourceSixOddBoundaryEnergy, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  simp only [show (⟨2, by omega⟩ : Fin 6) = 2 from rfl,
    show (⟨3, by omega⟩ : Fin 6) = 3 from rfl,
    show (⟨4, by omega⟩ : Fin 6) = 4 from rfl,
    show (⟨5, by omega⟩ : Fin 6) = 5 from rfl]
  ring

/-- Exactly ONE raw source integral inequality governs the new whole face. -/
theorem nativeSourceSixBoundaryEnergy_pos_iff_rawIntegral :
    (∀ x : Fin 6 → ℂ, x ≠ 0 → 0 < nativeSourceSixBoundaryEnergy x) ↔
      0 < nativeSourceTwelfthMixedNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) :=
  nativeSourceSixBoundaryEnergy_pos_iff.trans nativeSourceSixOddDiscriminant_pos_iff_rawIntegral

end
end CarrySelfAdjointOperator

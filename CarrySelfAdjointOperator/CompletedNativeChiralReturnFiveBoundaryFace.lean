import CarrySelfAdjointOperator.CompletedNativeChiralReturnNinthSourceJet

/-!
# Exact five-coordinate Green boundary face

This is the next boundary face of the existing alternating Green tower.
The odd block is reused unchanged. The even block has three coordinates.
Its exact square completion isolates one new raw-integral sign; no sign
is assumed or supplied by a canonical moment certificate. This face is
not substituted for the full radial storage at a nonzero step.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- The new even block retains all three pairwise crosses. -/
def nativeSourceFiveEvenBoundaryEnergy (u v w : ℂ) : ℝ :=
  nativeSourceOddBoundaryCoefficient 0 * Complex.normSq u -
    2 * nativeSourceOddBoundaryCoefficient 1 * (conj u*v).re +
    2 * nativeSourceOddBoundaryCoefficient 2 * (conj u*w).re +
    nativeSourceOddBoundaryCoefficient 2 * Complex.normSq v -
    2 * nativeSourceOddBoundaryCoefficient 3 * (conj v*w).re +
    nativeSourceOddBoundaryCoefficient 4 * Complex.normSq w

/-- The coefficient forced by elimination of the first two even boundary
coordinates. Defined from the original source derivatives, not a target Gram. -/
def nativeSourceFiveEvenDiscriminant : ℝ :=
  nativeSourceOddBoundaryCoefficient 0 * nativeSourceOddBoundaryCoefficient 2 *
      nativeSourceOddBoundaryCoefficient 4 +
    2 * nativeSourceOddBoundaryCoefficient 1 * nativeSourceOddBoundaryCoefficient 2 *
      nativeSourceOddBoundaryCoefficient 3 -
    nativeSourceOddBoundaryCoefficient 0 * nativeSourceOddBoundaryCoefficient 3^2 -
    nativeSourceOddBoundaryCoefficient 1^2 * nativeSourceOddBoundaryCoefficient 4 -
    nativeSourceOddBoundaryCoefficient 2^3

/-- Raw-integral polynomial fixed by the source recurrence and the mixed
Green boundary identity. This is an algebraic obstruction scalar, not a
new carrier, metric, operator or positivity assumption. -/
def nativeSourceTenthMixedNumerator (a b c d e f : ℝ) : ℝ :=
  105*a^2*b*d*f - 180*a^2*b*e^2 - 350*a^2*c^2*f +
    2520*a^2*c*d*e - 2646*a^2*d^3 + 525*a*b^2*c*f -
    2205*a*b^2*d*e - 9450*a*b*c^2*e + 26460*a*b*c*d^2 -
    14700*a*c^3*d + 14175*b^3*c*e - 35280*b^3*d^2 + 22050*b^2*c^2*d

/-- All factors, factorials and signs are certified directly from raw jets. -/
theorem nativeSourceFiveEvenDiscriminant_integral_formula :
    nativeSourceFiveEvenDiscriminant =
      nativeSourceTenthMixedNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5) /
        (4572288000 * completedNativeXiCosineMoment 0 ^ 5) := by
  obtain ⟨h0, h1, h2, h3⟩ := nativeSourceOddBoundaryCoefficient_integral_formulas
  unfold nativeSourceFiveEvenDiscriminant
  rw [h0, h1, h2, h3, nativeSourceOddBoundaryCoefficient_four_integral_formula]
  unfold nativeSourceTenthMixedNumerator nativeSourceSeventhNumerator nativeSourceNinthNumerator
  field_simp [(completedNativeXiCosineMoment_pos 0).ne']
  ring

/-- The new sign is exactly a raw integral inequality, with positive divisor. -/
theorem nativeSourceFiveEvenDiscriminant_pos_iff_rawIntegral :
    0 < nativeSourceFiveEvenDiscriminant ↔
      0 < nativeSourceTenthMixedNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5) := by
  rw [nativeSourceFiveEvenDiscriminant_integral_formula]
  exact div_pos_iff_of_pos_right (by positivity [completedNativeXiCosineMoment_pos 0])

/-- Exact square completion in the EXISTING complex norm, retaining crosses.
No square root, whitening, target matrix or change of metric is involved. -/
theorem nativeSourceFiveEvenBoundaryEnergy_square (u v w : ℂ) :
    let a := nativeSourceOddBoundaryCoefficient 0
    let b := nativeSourceOddBoundaryCoefficient 1
    let c := nativeSourceOddBoundaryCoefficient 2
    let d := nativeSourceOddBoundaryCoefficient 3
    let δ := a*c-b^2
    nativeSourceFiveEvenBoundaryEnergy u v w =
      a * Complex.normSq (u - ((b/a : ℝ) : ℂ)*v + ((c/a : ℝ) : ℂ)*w) +
      (δ/a) * Complex.normSq (v + (((b*c-a*d)/δ : ℝ) : ℂ)*w) +
      (nativeSourceFiveEvenDiscriminant/δ) * Complex.normSq w := by
  dsimp only
  have ha := nativeSourceMixedLeadingCoefficients_pos.1.ne'
  have hd := nativeSourceMixedDiscriminants_pos.1.ne'
  unfold nativeSourceFiveEvenBoundaryEnergy nativeSourceFiveEvenDiscriminant
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, add_zero, sub_zero]
  field_simp [ha, hd]
  ring

/-- Strict positivity of this new even FACE is equivalent to precisely one
new source sign. This equivalence neither assumes nor closes that sign. -/
theorem nativeSourceFiveEvenBoundaryEnergy_pos_iff :
    (∀ u v w : ℂ, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) →
      0 < nativeSourceFiveEvenBoundaryEnergy u v w) ↔
      0 < nativeSourceFiveEvenDiscriminant := by
  let a := nativeSourceOddBoundaryCoefficient 0
  let b := nativeSourceOddBoundaryCoefficient 1
  let c := nativeSourceOddBoundaryCoefficient 2
  let d := nativeSourceOddBoundaryCoefficient 3
  let δ := a*c-b^2
  have ha : 0 < a := nativeSourceMixedLeadingCoefficients_pos.1
  have hd : 0 < δ := nativeSourceMixedDiscriminants_pos.1
  constructor
  · intro hp
    let v : ℂ := (-((b*c-a*d)/δ : ℝ) : ℂ)
    let u : ℂ := ((b/a : ℝ) : ℂ)*v - ((c/a : ℝ) : ℂ)
    have ht := hp u v 1 (Or.inr (Or.inr one_ne_zero))
    rw [nativeSourceFiveEvenBoundaryEnergy_square] at ht
    change 0 < a * Complex.normSq (u - ((b/a : ℝ) : ℂ)*v + ((c/a : ℝ) : ℂ)*1) +
      (δ/a) * Complex.normSq (v + (((b*c-a*d)/δ : ℝ) : ℂ)*1) +
      (nativeSourceFiveEvenDiscriminant/δ) * Complex.normSq (1 : ℂ) at ht
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
    rw [nativeSourceFiveEvenBoundaryEnergy_square]
    change 0 < a * Complex.normSq (u - ((b/a : ℝ) : ℂ)*v + ((c/a : ℝ) : ℂ)*w) +
      (δ/a) * Complex.normSq (v + (((b*c-a*d)/δ : ℝ) : ℂ)*w) +
      (nativeSourceFiveEvenDiscriminant/δ) * Complex.normSq w
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

/-- Both parity sectors of the actual five-coordinate boundary face. -/
def nativeSourceFiveBoundaryEnergy (x : Fin 5 → ℂ) : ℝ :=
  2 * (nativeSourceFiveEvenBoundaryEnergy (x 0) (x 2) (x 4) +
    nativeSourceOddBoundaryEnergy (x 1) (x 3))


/-- The whole five-coordinate face, including the already-certified odd
sector, is positive precisely when the new even source discriminant is.
This is an exact localization of the open sign, not an assumption wrapper. -/
theorem nativeSourceFiveBoundaryEnergy_pos_iff :
    (∀ x : Fin 5 → ℂ, x ≠ 0 → 0 < nativeSourceFiveBoundaryEnergy x) ↔
      0 < nativeSourceFiveEvenDiscriminant := by
  constructor
  · intro h
    apply nativeSourceFiveEvenBoundaryEnergy_pos_iff.mp
    intro u v w hn
    let x : Fin 5 → ℂ := ![u, 0, v, 0, w]
    have hx : x ≠ 0 := by
      intro hz
      have h0 := congrFun hz 0
      have h2 := congrFun hz 2
      have h4 := congrFun hz 4
      simp [x] at h0 h2 h4
      tauto
    have ht := h x hx
    change 0 < 2 * (nativeSourceFiveEvenBoundaryEnergy u v w +
      nativeSourceOddBoundaryEnergy 0 0) at ht
    simp only [nativeSourceOddBoundaryEnergy, map_zero, mul_zero,
      Complex.zero_re, sub_zero, add_zero] at ht
    linarith
  · intro hn x hx
    have hp := nativeSourceFiveEvenBoundaryEnergy_pos_iff.mpr hn
    have he : 0 ≤ nativeSourceFiveEvenBoundaryEnergy (x 0) (x 2) (x 4) := by
      by_cases h : x 0 ≠ 0 ∨ x 2 ≠ 0 ∨ x 4 ≠ 0
      · exact (hp _ _ _ h).le
      · simp only [not_or, not_ne_iff] at h
        simp [nativeSourceFiveEvenBoundaryEnergy, h.1, h.2.1, h.2.2]
    have ho : 0 ≤ nativeSourceOddBoundaryEnergy (x 1) (x 3) := by
      by_cases h : x 1 ≠ 0 ∨ x 3 ≠ 0
      · exact (nativeSourceOddBoundaryEnergy_pos _ _ h).le
      · simp only [not_or, not_ne_iff] at h
        simp [nativeSourceOddBoundaryEnergy, h.1, h.2]
    have hnonzero : (x 0 ≠ 0 ∨ x 2 ≠ 0 ∨ x 4 ≠ 0) ∨ (x 1 ≠ 0 ∨ x 3 ≠ 0) := by
      by_contra h
      simp only [not_or, not_ne_iff] at h
      apply hx
      funext i
      fin_cases i <;> simp [h]
    unfold nativeSourceFiveBoundaryEnergy
    rcases hnonzero with hn | hn
    · exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg (hp _ _ _ hn) ho)
    · exact mul_pos (by norm_num) (add_pos_of_nonneg_of_pos he
        (nativeSourceOddBoundaryEnergy_pos _ _ hn))

/-- Zero extension exposes only the limiting finite jet face. It does not
set the higher jets of the actual source to zero at any finite radial step. -/
def nativeSourceFiveBoundaryExtension (x : Fin 5 → ℂ) (m : ℕ) : ℂ :=
  if h : m < 5 then x ⟨m, h⟩ else 0

/-- Exact identification with the EXISTING polarized Green boundary tower. -/
theorem nativeSourceFiveBoundaryEnergy_eq_alternating_green (x : Fin 5 → ℂ) :
    nativeSourceFiveBoundaryEnergy x =
      2 * ∑ j ∈ Finset.range 5, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
        (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
          (conj (nativeSourceFiveBoundaryExtension x a) *
            nativeSourceFiveBoundaryExtension x (2*j-a)).re) := by
  norm_num [Finset.sum_range_succ, nativeSourceFiveBoundaryExtension,
    nativeSourceFiveBoundaryEnergy, nativeSourceFiveEvenBoundaryEnergy,
    nativeSourceOddBoundaryEnergy, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  simp only [show (⟨2, by omega⟩ : Fin 5) = 2 from rfl,
    show (⟨3, by omega⟩ : Fin 5) = 3 from rfl,
    show (⟨4, by omega⟩ : Fin 5) = 4 from rfl]
  ring

/-- The order-ten raw integral enters affinely with a coefficient already
certified positive by the previous source integral gate. -/
theorem nativeSourceTenthMixedNumerator_eq_affine_lastIntegral (a b c d e f : ℝ) :
    nativeSourceTenthMixedNumerator a b c d e f =
      35*a*(15*b^2*c+3*a*b*d-10*a*c^2)*f +
        nativeSourceTenthMixedNumerator a b c d e 0 := by
  unfold nativeSourceTenthMixedNumerator
  ring

/-- A single explicit raw integral lower bound is EXACTLY the remaining
new even-face sign. No positivity hypothesis wrapper is introduced. -/
theorem nativeSourceFiveEvenDiscriminant_pos_iff_tenthIntegralBound :
    0 < nativeSourceFiveEvenDiscriminant ↔
      -nativeSourceTenthMixedNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) 0 /
        (35 * completedNativeXiCosineMoment 0 *
          (15 * completedNativeXiCosineMoment 1 ^ 2 * completedNativeXiCosineMoment 2 +
            3 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 1 *
              completedNativeXiCosineMoment 3 -
            10 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 ^ 2)) <
        completedNativeXiCosineMoment 5 := by
  rw [nativeSourceFiveEvenDiscriminant_pos_iff_rawIntegral,
    nativeSourceTenthMixedNumerator_eq_affine_lastIntegral]
  have hpos := mul_pos (mul_pos (by norm_num : (0:ℝ)<35)
    (completedNativeXiCosineMoment_pos 0)) nativeSourceSixthMixedNumerator_pos
  rw [div_lt_iff₀ hpos]
  constructor <;> intro h <;> linarith


/-- The existing refined raw-integral box and the two previously certified
mixed signs, EVEN TOGETHER WITH a positive ninth derivative, do not force the
new sign. This rational point is an exact counterexample to that inference;
it is NOT the actual completed source and refutes no source positivity. -/
theorem nativeSourceRefinedBox_does_not_force_fiveEvenSign :
    ∃ a b c d e f : ℝ,
      (7767507 / 15625000 : ℝ) ≤ a ∧ a ≤ 19884837 / 40000000 ∧
      (574269 / 25000000 : ℝ) ≤ b ∧ b ≤ 22974587 / 1000000000 ∧
      (2962661 / 1000000000 : ℝ) ≤ c ∧ c ≤ 740861 / 250000000 ∧
      (299619 / 500000000 : ℝ) ≤ d ∧ d ≤ 600193 / 1000000000 ∧
      (10059 / 62500000 : ℝ) ≤ e ∧ e ≤ 161051 / 1000000000 ∧
      0 < f ∧ 0 < 15*b^2*c+3*a*b*d-10*a*c^2 ∧
      0 < xiEighthMomentNumerator a b c d e ∧
      0 < nativeSourceNinthNumerator a b c d e f ∧
      nativeSourceTenthMixedNumerator a b c d e f < 0 := by
  refine ⟨19884837/40000000, 574269/25000000, 740861/250000000,
    299619/500000000, 161051/1000000000, 53/1000000, ?_⟩
  norm_num [xiEighthMomentNumerator, nativeSourceNinthNumerator,
    nativeSourceTenthMixedNumerator]

end
end CarrySelfAdjointOperator

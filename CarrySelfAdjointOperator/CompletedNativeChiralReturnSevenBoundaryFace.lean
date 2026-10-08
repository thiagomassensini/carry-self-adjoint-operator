import CarrySelfAdjointOperator.CompletedNativeChiralReturnTwelfthSourceIntegral
import CarrySelfAdjointOperator.CompletedNativeChiralReturnThirteenthSourceJet
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenRemainderBound

/-!
# Complete seven-coordinate Green boundary face

The four even coordinates and three odd coordinates are fixed by the
original alternating Green tower. The existing three-coordinate faces
are retained. The fourth even coordinate introduces one exact source
scalar. No sign of that scalar, metric fitting or moment input occurs.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-- All six even pairwise crosses from the original source boundary tower. -/
def nativeSourceSevenEvenBoundaryEnergy (u v w t : ℂ) : ℝ :=
  nativeSourceFiveEvenBoundaryEnergy u v w -
    2 * nativeSourceOddBoundaryCoefficient 3 * (conj u*t).re +
    2 * nativeSourceOddBoundaryCoefficient 4 * (conj v*t).re -
    2 * nativeSourceOddBoundaryCoefficient 5 * (conj w*t).re +
    nativeSourceOddBoundaryCoefficient 6 * Complex.normSq t

/-- Numerators fixed by the old three-coordinate source form and its actual
coupling to the new coordinate. These do not modify the form or its norm. -/
def nativeSourceSevenEvenCoupling0 : ℝ :=
  let a := nativeSourceOddBoundaryCoefficient 1
  let b := nativeSourceOddBoundaryCoefficient 2
  let c := nativeSourceOddBoundaryCoefficient 3
  let d := nativeSourceOddBoundaryCoefficient 4
  let e := nativeSourceOddBoundaryCoefficient 5
  a*d^2 - 2*b*c*d + c^3 - a*c*e + b^2*e

def nativeSourceSevenEvenCoupling1 : ℝ :=
  let a := nativeSourceOddBoundaryCoefficient 0
  let b := nativeSourceOddBoundaryCoefficient 1
  let c := nativeSourceOddBoundaryCoefficient 2
  let d := nativeSourceOddBoundaryCoefficient 3
  let e := nativeSourceOddBoundaryCoefficient 4
  let f := nativeSourceOddBoundaryCoefficient 5
  a*e^2 - b*d*e + c*d^2 - c^2*e - a*d*f + b*c*f

def nativeSourceSevenEvenCoupling2 : ℝ :=
  let a := nativeSourceOddBoundaryCoefficient 0
  let b := nativeSourceOddBoundaryCoefficient 1
  let c := nativeSourceOddBoundaryCoefficient 2
  let d := nativeSourceOddBoundaryCoefficient 3
  let e := nativeSourceOddBoundaryCoefficient 4
  let f := nativeSourceOddBoundaryCoefficient 5
  a*d*e - b*c*e - b*d^2 + c^2*d - a*c*f + b^2*f

/-- The last source scalar left by the exact polarized boundary identity.
It depends on the original source coefficients, not on a canonical target. -/
def nativeSourceSevenEvenDiscriminant : ℝ :=
  nativeSourceFiveEvenDiscriminant * nativeSourceOddBoundaryCoefficient 6 +
    nativeSourceOddBoundaryCoefficient 3 * nativeSourceSevenEvenCoupling0 -
    nativeSourceOddBoundaryCoefficient 4 * nativeSourceSevenEvenCoupling1 +
    nativeSourceOddBoundaryCoefficient 5 * nativeSourceSevenEvenCoupling2

/-- Exact identity in the existing complex norm, with EVERY cross retained.
Only the already-positive three-coordinate source divisor is used. -/
theorem nativeSourceSevenEvenBoundaryEnergy_sewing (u v w t : ℂ) :
    let δ := nativeSourceFiveEvenDiscriminant
    nativeSourceSevenEvenBoundaryEnergy u v w t =
      nativeSourceFiveEvenBoundaryEnergy
        (u + ((nativeSourceSevenEvenCoupling0/δ : ℝ) : ℂ)*t)
        (v + ((nativeSourceSevenEvenCoupling1/δ : ℝ) : ℂ)*t)
        (w + ((nativeSourceSevenEvenCoupling2/δ : ℝ) : ℂ)*t) +
      (nativeSourceSevenEvenDiscriminant/δ) * Complex.normSq t := by
  dsimp only
  have hd := nativeSourceFiveEvenDiscriminant_pos.ne'
  generalize hδ : nativeSourceFiveEvenDiscriminant = δ at *
  unfold nativeSourceSevenEvenBoundaryEnergy nativeSourceFiveEvenBoundaryEnergy
    nativeSourceSevenEvenDiscriminant nativeSourceSevenEvenCoupling0
    nativeSourceSevenEvenCoupling1 nativeSourceSevenEvenCoupling2
  simp only [hδ]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, add_zero, sub_zero]
  field_simp [hd]
  rw [← hδ]
  unfold nativeSourceFiveEvenDiscriminant
  ring

/-- Exactly one new source sign is equivalent to positivity of the entire
four-coordinate even face. No sign premise is introduced by this equivalence. -/
theorem nativeSourceSevenEvenBoundaryEnergy_pos_iff :
    (∀ u v w t : ℂ, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0 ∨ t ≠ 0) →
      0 < nativeSourceSevenEvenBoundaryEnergy u v w t) ↔
      0 < nativeSourceSevenEvenDiscriminant := by
  constructor
  · intro hp
    let u : ℂ := -((nativeSourceSevenEvenCoupling0/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ)
    let v : ℂ := -((nativeSourceSevenEvenCoupling1/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ)
    let w : ℂ := -((nativeSourceSevenEvenCoupling2/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ)
    have ht := hp u v w 1 (Or.inr (Or.inr (Or.inr one_ne_zero)))
    rw [nativeSourceSevenEvenBoundaryEnergy_sewing] at ht
    simp only [u,v,w,mul_one,neg_add_cancel,Complex.normSq_one,mul_one] at ht
    simp only [nativeSourceFiveEvenBoundaryEnergy,
      map_zero, mul_zero, Complex.zero_re, zero_add, add_zero, sub_zero] at ht
    exact (div_pos_iff_of_pos_right nativeSourceFiveEvenDiscriminant_pos).mp ht
  · intro hnew u v w t hn
    rw [nativeSourceSevenEvenBoundaryEnergy_sewing]
    by_cases ht : t = 0
    · rw [ht]
      simp only [mul_zero, add_zero, Complex.normSq_zero]
      exact nativeSourceFiveEvenBoundaryEnergy_pos u v w (by tauto)
    · have hQ : 0 ≤ nativeSourceFiveEvenBoundaryEnergy
          (u + ((nativeSourceSevenEvenCoupling0/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ)*t)
          (v + ((nativeSourceSevenEvenCoupling1/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ)*t)
          (w + ((nativeSourceSevenEvenCoupling2/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ)*t) := by
        rw [nativeSourceFiveEvenBoundaryEnergy_square]
        exact add_nonneg (add_nonneg
          (mul_nonneg nativeSourceMixedLeadingCoefficients_pos.1.le (Complex.normSq_nonneg _))
          (mul_nonneg (div_pos nativeSourceMixedDiscriminants_pos.1
            nativeSourceMixedLeadingCoefficients_pos.1).le (Complex.normSq_nonneg _)))
          (mul_nonneg (div_pos nativeSourceFiveEvenDiscriminant_pos
            nativeSourceMixedDiscriminants_pos.1).le (Complex.normSq_nonneg _))
      exact add_pos_of_nonneg_of_pos hQ
        (mul_pos (div_pos hnew nativeSourceFiveEvenDiscriminant_pos) (Complex.normSq_pos.mpr ht))

/-- Both COMPLETE parity sectors of the original seven-coordinate face. -/
def nativeSourceSevenBoundaryEnergy (x : Fin 7 → ℂ) : ℝ :=
  2 * (nativeSourceSevenEvenBoundaryEnergy (x 0) (x 2) (x 4) (x 6) +
    nativeSourceSixOddBoundaryEnergy (x 1) (x 3) (x 5))

/-- Limiting coordinate extension only; no finite-step tail is discarded. -/
def nativeSourceSevenBoundaryExtension (x : Fin 7 → ℂ) (m : ℕ) : ℂ :=
  if h : m < 7 then x ⟨m,h⟩ else 0

/-- The actual signed tower determines every coefficient and cross term. -/
theorem nativeSourceSevenBoundaryEnergy_eq_alternating_green (x : Fin 7 → ℂ) :
    nativeSourceSevenBoundaryEnergy x =
      2 * ∑ j ∈ Finset.range 7, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
        (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
          (conj (nativeSourceSevenBoundaryExtension x a) *
            nativeSourceSevenBoundaryExtension x (2*j-a)).re) := by
  norm_num [Finset.sum_range_succ, nativeSourceSevenBoundaryExtension,
    nativeSourceSevenBoundaryEnergy, nativeSourceSevenEvenBoundaryEnergy,
    nativeSourceFiveEvenBoundaryEnergy, nativeSourceSixOddBoundaryEnergy,
    Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp only [show (⟨2, by omega⟩ : Fin 7) = 2 from rfl,
    show (⟨3, by omega⟩ : Fin 7) = 3 from rfl,
    show (⟨4, by omega⟩ : Fin 7) = 4 from rfl,
    show (⟨5, by omega⟩ : Fin 7) = 5 from rfl,
    show (⟨6, by omega⟩ : Fin 7) = 6 from rfl]
  ring

/-- The old odd face is certified. Exactly ONE even source sign remains. -/
theorem nativeSourceSevenBoundaryEnergy_pos_iff :
    (∀ x : Fin 7 → ℂ, x ≠ 0 → 0 < nativeSourceSevenBoundaryEnergy x) ↔
      0 < nativeSourceSevenEvenDiscriminant := by
  constructor
  · intro hp
    apply nativeSourceSevenEvenBoundaryEnergy_pos_iff.mp
    intro u v w t hn
    let x : Fin 7 → ℂ := ![u,0,v,0,w,0,t]
    have hx : x ≠ 0 := by
      intro hz
      have h0 := congrFun hz 0
      have h2 := congrFun hz 2
      have h4 := congrFun hz 4
      have h6 := congrFun hz 6
      simp [x] at h0 h2 h4 h6
      tauto
    have ht := hp x hx
    change 0 < 2 * (nativeSourceSevenEvenBoundaryEnergy u v w t +
      nativeSourceSixOddBoundaryEnergy 0 0 0) at ht
    simp only [nativeSourceSixOddBoundaryEnergy, map_zero, mul_zero,
      Complex.zero_re, sub_zero, add_zero] at ht
    linarith
  · intro hs x hx
    have he := nativeSourceSevenEvenBoundaryEnergy_pos_iff.mpr hs
    have ho : 0 ≤ nativeSourceSixOddBoundaryEnergy (x 1) (x 3) (x 5) := by
      by_cases h : x 1 ≠ 0 ∨ x 3 ≠ 0 ∨ x 5 ≠ 0
      · exact (nativeSourceSixOddBoundaryEnergy_pos _ _ _ h).le
      · simp only [not_or, not_ne_iff] at h
        simp [nativeSourceSixOddBoundaryEnergy,h.1,h.2.1,h.2.2]
    have hev : 0 ≤ nativeSourceSevenEvenBoundaryEnergy (x 0) (x 2) (x 4) (x 6) := by
      by_cases h : x 0 ≠ 0 ∨ x 2 ≠ 0 ∨ x 4 ≠ 0 ∨ x 6 ≠ 0
      · exact (he _ _ _ _ h).le
      · simp only [not_or, not_ne_iff] at h
        simp [nativeSourceSevenEvenBoundaryEnergy,nativeSourceFiveEvenBoundaryEnergy,
          h.1,h.2.1,h.2.2.1,h.2.2.2]
    have hn : (x 0 ≠ 0 ∨ x 2 ≠ 0 ∨ x 4 ≠ 0 ∨ x 6 ≠ 0) ∨
        (x 1 ≠ 0 ∨ x 3 ≠ 0 ∨ x 5 ≠ 0) := by
      by_contra h
      simp only [not_or, not_ne_iff] at h
      apply hx
      funext i
      fin_cases i <;> simp [h]
    unfold nativeSourceSevenBoundaryEnergy
    rcases hn with hn | hn
    · exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg (he _ _ _ _ hn) ho)
    · exact mul_pos (by norm_num) (add_pos_of_nonneg_of_pos hev
        (nativeSourceSixOddBoundaryEnergy_pos _ _ _ hn))


/-- Continuity uses the unchanged finite coordinate norm and actual source coefficients. -/
theorem nativeSourceSevenBoundaryEnergy_continuous :
    Continuous nativeSourceSevenBoundaryEnergy := by
  unfold nativeSourceSevenBoundaryEnergy nativeSourceSevenEvenBoundaryEnergy
    nativeSourceFiveEvenBoundaryEnergy nativeSourceSixOddBoundaryEnergy
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  fun_prop

/-- Real quadratic homogeneity; no coordinate rescaling changes the form. -/
theorem nativeSourceSevenBoundaryEnergy_real_smul (a : ℝ) (x : Fin 7 → ℂ) :
    nativeSourceSevenBoundaryEnergy ((a : ℂ) • x) =
      a^2 * nativeSourceSevenBoundaryEnergy x := by
  unfold nativeSourceSevenBoundaryEnergy nativeSourceSevenEvenBoundaryEnergy
    nativeSourceFiveEvenBoundaryEnergy nativeSourceSixOddBoundaryEnergy
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The requested UNIFORM margin for the COMPLETE seven-coordinate boundary
face is equivalent to one unchanged source sign. This is an equivalence,
not an assumption wrapper or a proof of that sign. -/
theorem nativeSourceSevenBoundaryEnergy_uniform_margin_iff :
    (∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin 7 → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceSevenBoundaryEnergy x) ↔
      0 < nativeSourceSevenEvenDiscriminant := by
  constructor
  · rintro ⟨ε, he, hb⟩
    apply nativeSourceSevenBoundaryEnergy_pos_iff.mp
    intro x hx
    exact lt_of_lt_of_le (mul_pos he (sq_pos_of_pos (norm_pos_iff.mpr hx))) (hb x)
  · intro hs
    have hp := nativeSourceSevenBoundaryEnergy_pos_iff.mpr hs
    let K : Set (Fin 7 → ℂ) := Metric.sphere 0 1
    have hK : IsCompact K := isCompact_sphere 0 1
    have hne : K.Nonempty := by
      refine ⟨(1 : Fin 7 → ℂ), ?_⟩
      simp [K]
    obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne
      nativeSourceSevenBoundaryEnergy_continuous.continuousOn
    have hn₀ : x₀ ≠ 0 := by intro he; simp [K, he] at hx₀
    refine ⟨nativeSourceSevenBoundaryEnergy x₀, hp x₀ hn₀, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx, nativeSourceSevenBoundaryEnergy, nativeSourceSevenEvenBoundaryEnergy,
        nativeSourceFiveEvenBoundaryEnergy, nativeSourceSixOddBoundaryEnergy]
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      let y := ((‖x‖⁻¹ : ℝ) : ℂ) • x
      have hy : y ∈ K := by
        change dist y 0 = 1
        rw [dist_zero_right]
        dsimp only [y]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
          inv_mul_cancel₀ hn]
      have hb := hmin hy
      change nativeSourceSevenBoundaryEnergy x₀ ≤
        nativeSourceSevenBoundaryEnergy (((‖x‖⁻¹ : ℝ) : ℂ) • x) at hb
      rw [nativeSourceSevenBoundaryEnergy_real_smul] at hb
      have hr : ‖x‖^2 * (‖x‖⁻¹)^2 = 1 := by field_simp [hn]
      have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖x‖)
      calc
        nativeSourceSevenBoundaryEnergy x₀ * ‖x‖^2 =
          ‖x‖^2 * nativeSourceSevenBoundaryEnergy x₀ := by ring
        _ ≤ ‖x‖^2 * ((‖x‖⁻¹)^2 * nativeSourceSevenBoundaryEnergy x) := hm
        _ = nativeSourceSevenBoundaryEnergy x := by rw [← mul_assoc, hr, one_mul]

/-- The exact remaining inequality involves ONLY the raw completed source. -/
theorem nativeSourceSevenEvenDiscriminant_pos_iff_coefficient_gap :
    0 < nativeSourceSevenEvenDiscriminant ↔
      (-nativeSourceOddBoundaryCoefficient 3 * nativeSourceSevenEvenCoupling0 +
        nativeSourceOddBoundaryCoefficient 4 * nativeSourceSevenEvenCoupling1 -
        nativeSourceOddBoundaryCoefficient 5 * nativeSourceSevenEvenCoupling2) /
          nativeSourceFiveEvenDiscriminant < nativeSourceOddBoundaryCoefficient 6 := by
  rw [div_lt_iff₀ nativeSourceFiveEvenDiscriminant_pos]
  unfold nativeSourceSevenEvenDiscriminant
  constructor <;> intro h <;> nlinarith

/-- An exact nonzero source chart tests the remaining scalar without dropping
ANY cross term. It is a diagnostic vector, not a replacement source. -/
def nativeSourceSevenBoundaryPivot : Fin 7 → ℂ :=
  ![-((nativeSourceSevenEvenCoupling0/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ),
    0, -((nativeSourceSevenEvenCoupling1/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ),
    0, -((nativeSourceSevenEvenCoupling2/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ), 0, 1]

theorem nativeSourceSevenBoundaryPivot_ne_zero : nativeSourceSevenBoundaryPivot ≠ 0 := by
  intro hz
  have h := congrFun hz 6
  change (1 : ℂ) = 0 at h
  exact one_ne_zero h

theorem nativeSourceSevenBoundaryPivot_energy :
    nativeSourceSevenBoundaryEnergy nativeSourceSevenBoundaryPivot =
      2 * (nativeSourceSevenEvenDiscriminant/nativeSourceFiveEvenDiscriminant) := by
  change 2 * (nativeSourceSevenEvenBoundaryEnergy
    (-((nativeSourceSevenEvenCoupling0/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ))
    (-((nativeSourceSevenEvenCoupling1/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ))
    (-((nativeSourceSevenEvenCoupling2/nativeSourceFiveEvenDiscriminant : ℝ) : ℂ)) 1 +
    nativeSourceSixOddBoundaryEnergy 0 0 0) = _
  rw [nativeSourceSevenEvenBoundaryEnergy_sewing]
  simp [nativeSourceFiveEvenBoundaryEnergy, nativeSourceSixOddBoundaryEnergy]


/-- The entire seven-coordinate margin is now EXACTLY a raw integral
inequality. No canonical moment, certificate or downstream sign is used. -/
theorem nativeSourceSevenBoundaryEnergy_uniform_margin_iff_integral_gap :
    (∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin 7 → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceSevenBoundaryEnergy x) ↔
      (-nativeSourceOddBoundaryCoefficient 3 * nativeSourceSevenEvenCoupling0 +
        nativeSourceOddBoundaryCoefficient 4 * nativeSourceSevenEvenCoupling1 -
        nativeSourceOddBoundaryCoefficient 5 * nativeSourceSevenEvenCoupling2) /
          nativeSourceFiveEvenDiscriminant <
      nativeSourceThirteenthNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) (completedNativeXiCosineMoment 7) /
          (6227020800 * completedNativeXiCosineMoment 0^7) := by
  rw [nativeSourceSevenBoundaryEnergy_uniform_margin_iff,
    nativeSourceSevenEvenDiscriminant_pos_iff_coefficient_gap,
    nativeSourceOddBoundaryCoefficient_six_integral_formula]

end
end CarrySelfAdjointOperator

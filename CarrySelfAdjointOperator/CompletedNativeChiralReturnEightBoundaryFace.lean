import CarrySelfAdjointOperator.CompletedNativeChiralReturnArbitraryOrder

/-!
# The first uncertified boundary extension: eight original sources

The old even four-coordinate face is positive. The new odd coordinate leaves
one scalar from the actual source derivatives. Every coupling is retained.
The exact reduction below does not establish the sign of that scalar.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-- All six odd pairwise crosses from the original source boundary tower. -/
def nativeSourceEightOddBoundaryEnergy (u v w t : ℂ) : ℝ :=
  nativeSourceSixOddBoundaryEnergy u v w -
    2 * nativeSourceOddBoundaryCoefficient 4 * (conj u*t).re +
    2 * nativeSourceOddBoundaryCoefficient 5 * (conj v*t).re -
    2 * nativeSourceOddBoundaryCoefficient 6 * (conj w*t).re +
    nativeSourceOddBoundaryCoefficient 7 * Complex.normSq t

/-- Numerators fixed by the old three-coordinate source form and its actual
coupling to the new coordinate. These do not modify the form or its norm. -/
def nativeSourceEightOddCoupling0 : ℝ :=
  let a := nativeSourceOddBoundaryCoefficient 2
  let b := nativeSourceOddBoundaryCoefficient 3
  let c := nativeSourceOddBoundaryCoefficient 4
  let d := nativeSourceOddBoundaryCoefficient 5
  let e := nativeSourceOddBoundaryCoefficient 6
  a*d^2 - 2*b*c*d + c^3 - a*c*e + b^2*e

def nativeSourceEightOddCoupling1 : ℝ :=
  let a := nativeSourceOddBoundaryCoefficient 1
  let b := nativeSourceOddBoundaryCoefficient 2
  let c := nativeSourceOddBoundaryCoefficient 3
  let d := nativeSourceOddBoundaryCoefficient 4
  let e := nativeSourceOddBoundaryCoefficient 5
  let f := nativeSourceOddBoundaryCoefficient 6
  a*e^2 - b*d*e + c*d^2 - c^2*e - a*d*f + b*c*f

def nativeSourceEightOddCoupling2 : ℝ :=
  let a := nativeSourceOddBoundaryCoefficient 1
  let b := nativeSourceOddBoundaryCoefficient 2
  let c := nativeSourceOddBoundaryCoefficient 3
  let d := nativeSourceOddBoundaryCoefficient 4
  let e := nativeSourceOddBoundaryCoefficient 5
  let f := nativeSourceOddBoundaryCoefficient 6
  a*d*e - b*c*e - b*d^2 + c^2*d - a*c*f + b^2*f

/-- The last source scalar left by the exact polarized boundary identity.
It depends on the original source coefficients, not on a canonical target. -/
def nativeSourceEightOddDiscriminant : ℝ :=
  nativeSourceSixOddDiscriminant * nativeSourceOddBoundaryCoefficient 7 +
    nativeSourceOddBoundaryCoefficient 4 * nativeSourceEightOddCoupling0 -
    nativeSourceOddBoundaryCoefficient 5 * nativeSourceEightOddCoupling1 +
    nativeSourceOddBoundaryCoefficient 6 * nativeSourceEightOddCoupling2

/-- Exact identity in the existing complex norm, with EVERY cross retained.
Only the already-positive three-coordinate source divisor is used. -/
theorem nativeSourceEightOddBoundaryEnergy_sewing (u v w t : ℂ) :
    let δ := nativeSourceSixOddDiscriminant
    nativeSourceEightOddBoundaryEnergy u v w t =
      nativeSourceSixOddBoundaryEnergy
        (u + ((nativeSourceEightOddCoupling0/δ : ℝ) : ℂ)*t)
        (v + ((nativeSourceEightOddCoupling1/δ : ℝ) : ℂ)*t)
        (w + ((nativeSourceEightOddCoupling2/δ : ℝ) : ℂ)*t) +
      (nativeSourceEightOddDiscriminant/δ) * Complex.normSq t := by
  dsimp only
  have hd := nativeSourceSixOddDiscriminant_pos.ne'
  generalize hδ : nativeSourceSixOddDiscriminant = δ at *
  unfold nativeSourceEightOddBoundaryEnergy nativeSourceSixOddBoundaryEnergy
    nativeSourceEightOddDiscriminant nativeSourceEightOddCoupling0
    nativeSourceEightOddCoupling1 nativeSourceEightOddCoupling2
  simp only [hδ]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, add_zero, sub_zero]
  field_simp [hd]
  rw [← hδ]
  unfold nativeSourceSixOddDiscriminant
  ring

/-- Exactly one new source sign is equivalent to positivity of the entire
four-coordinate odd face. No sign premise is introduced by this equivalence. -/
theorem nativeSourceEightOddBoundaryEnergy_pos_iff :
    (∀ u v w t : ℂ, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0 ∨ t ≠ 0) →
      0 < nativeSourceEightOddBoundaryEnergy u v w t) ↔
      0 < nativeSourceEightOddDiscriminant := by
  constructor
  · intro hp
    let u : ℂ := -((nativeSourceEightOddCoupling0/nativeSourceSixOddDiscriminant : ℝ) : ℂ)
    let v : ℂ := -((nativeSourceEightOddCoupling1/nativeSourceSixOddDiscriminant : ℝ) : ℂ)
    let w : ℂ := -((nativeSourceEightOddCoupling2/nativeSourceSixOddDiscriminant : ℝ) : ℂ)
    have ht := hp u v w 1 (Or.inr (Or.inr (Or.inr one_ne_zero)))
    rw [nativeSourceEightOddBoundaryEnergy_sewing] at ht
    simp only [u,v,w,mul_one,neg_add_cancel,Complex.normSq_one,mul_one] at ht
    simp only [nativeSourceSixOddBoundaryEnergy,
      map_zero, mul_zero, Complex.zero_re, zero_add, add_zero, sub_zero] at ht
    exact (div_pos_iff_of_pos_right nativeSourceSixOddDiscriminant_pos).mp ht
  · intro hnew u v w t hn
    rw [nativeSourceEightOddBoundaryEnergy_sewing]
    by_cases ht : t = 0
    · rw [ht]
      simp only [mul_zero, add_zero, Complex.normSq_zero]
      exact nativeSourceSixOddBoundaryEnergy_pos u v w (by tauto)
    · have hQ : 0 ≤ nativeSourceSixOddBoundaryEnergy
          (u + ((nativeSourceEightOddCoupling0/nativeSourceSixOddDiscriminant : ℝ) : ℂ)*t)
          (v + ((nativeSourceEightOddCoupling1/nativeSourceSixOddDiscriminant : ℝ) : ℂ)*t)
          (w + ((nativeSourceEightOddCoupling2/nativeSourceSixOddDiscriminant : ℝ) : ℂ)*t) := by
        rw [nativeSourceSixOddBoundaryEnergy_square]
        exact add_nonneg (add_nonneg
          (mul_nonneg nativeSourceMixedLeadingCoefficients_pos.2.le (Complex.normSq_nonneg _))
          (mul_nonneg (div_pos nativeSourceMixedDiscriminants_pos.2
            nativeSourceMixedLeadingCoefficients_pos.2).le (Complex.normSq_nonneg _)))
          (mul_nonneg (div_pos nativeSourceSixOddDiscriminant_pos
            nativeSourceMixedDiscriminants_pos.2).le (Complex.normSq_nonneg _))
      exact add_pos_of_nonneg_of_pos hQ
        (mul_pos (div_pos hnew nativeSourceSixOddDiscriminant_pos) (Complex.normSq_pos.mpr ht))

/-- The nonpositive pivot has an explicit nonzero critical source direction. -/
theorem nativeSourceEightOddBoundaryEnergy_critical_direction :
    nativeSourceEightOddBoundaryEnergy
      (-((nativeSourceEightOddCoupling0/nativeSourceSixOddDiscriminant : ℝ) : ℂ))
      (-((nativeSourceEightOddCoupling1/nativeSourceSixOddDiscriminant : ℝ) : ℂ))
      (-((nativeSourceEightOddCoupling2/nativeSourceSixOddDiscriminant : ℝ) : ℂ)) 1 =
        nativeSourceEightOddDiscriminant / nativeSourceSixOddDiscriminant := by
  rw [nativeSourceEightOddBoundaryEnergy_sewing]
  simp [nativeSourceSixOddBoundaryEnergy]

/-- Both complete parity sectors, now with four original sources in each. -/
def nativeSourceEightBoundaryEnergy (x : Fin 8 → ℂ) : ℝ :=
  2 * (nativeSourceSevenEvenBoundaryEnergy (x 0) (x 2) (x 4) (x 6) +
    nativeSourceEightOddBoundaryEnergy (x 1) (x 3) (x 5) (x 7))

/-- Exact original source form, before any test of its sign. -/
theorem nativeSourceFiniteBoundaryEnergy_eight (x : Fin 8 → ℂ) :
    nativeSourceFiniteBoundaryEnergy 8 x = nativeSourceEightBoundaryEnergy x := by
  norm_num [nativeSourceFiniteBoundaryEnergy, Finset.sum_range_succ,
    nativeSourceEightBoundaryEnergy, nativeSourceSevenEvenBoundaryEnergy,
    nativeSourceFiveEvenBoundaryEnergy, nativeSourceEightOddBoundaryEnergy,
    nativeSourceSixOddBoundaryEnergy,
    Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp only [show (⟨2, by omega⟩ : Fin 8) = 2 from rfl,
    show (⟨3, by omega⟩ : Fin 8) = 3 from rfl,
    show (⟨4, by omega⟩ : Fin 8) = 4 from rfl,
    show (⟨5, by omega⟩ : Fin 8) = 5 from rfl,
    show (⟨6, by omega⟩ : Fin 8) = 6 from rfl,
    show (⟨7, by omega⟩ : Fin 8) = 7 from rfl]
  ring

/-- The entire eight-source sign is equivalent to one concrete new scalar.
The old even face is used with its existing unconditional source certificate. -/
theorem nativeSourceFiniteBoundaryEnergy_eight_pos_iff :
    (∀ x : Fin 8 → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy 8 x) ↔
      0 < nativeSourceEightOddDiscriminant := by
  constructor
  · intro hp
    apply nativeSourceEightOddBoundaryEnergy_pos_iff.mp
    intro u v w t hn
    let x : Fin 8 → ℂ := ![0,u,0,v,0,w,0,t]
    have hx : x ≠ 0 := by
      intro hz
      have h1 := congrFun hz 1
      have h3 := congrFun hz 3
      have h5 := congrFun hz 5
      have h7 := congrFun hz 7
      simp [x] at h1 h3 h5 h7
      tauto
    have h := hp x hx
    rw [nativeSourceFiniteBoundaryEnergy_eight] at h
    have he : nativeSourceEightBoundaryEnergy x =
        2 * nativeSourceEightOddBoundaryEnergy u v w t := by
      change 2 * (nativeSourceSevenEvenBoundaryEnergy 0 0 0 0 +
        nativeSourceEightOddBoundaryEnergy u v w t) = _
      simp [nativeSourceSevenEvenBoundaryEnergy, nativeSourceFiveEvenBoundaryEnergy]
    rw [he] at h
    linarith
  · intro hd x hx
    rw [nativeSourceFiniteBoundaryEnergy_eight, nativeSourceEightBoundaryEnergy]
    have he := nativeSourceSevenEvenBoundaryEnergy_pos
    have ho := nativeSourceEightOddBoundaryEnergy_pos_iff.mpr hd
    by_cases hE : x 0 ≠ 0 ∨ x 2 ≠ 0 ∨ x 4 ≠ 0 ∨ x 6 ≠ 0
    · have hO : 0 ≤ nativeSourceEightOddBoundaryEnergy (x 1) (x 3) (x 5) (x 7) := by
        by_cases hO : x 1 ≠ 0 ∨ x 3 ≠ 0 ∨ x 5 ≠ 0 ∨ x 7 ≠ 0
        · exact (ho _ _ _ _ hO).le
        · push Not at hO
          simp [hO.1, hO.2.1, hO.2.2.1, hO.2.2.2,
            nativeSourceEightOddBoundaryEnergy, nativeSourceSixOddBoundaryEnergy]
      exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg (he _ _ _ _ hE) hO)
    · push Not at hE
      have hO : x 1 ≠ 0 ∨ x 3 ≠ 0 ∨ x 5 ≠ 0 ∨ x 7 ≠ 0 := by
        by_contra hn
        push Not at hn
        apply hx
        funext i
        fin_cases i <;> simp_all
      have hEzero : nativeSourceSevenEvenBoundaryEnergy (x 0) (x 2) (x 4) (x 6) = 0 := by
        simp [hE.1, hE.2.1, hE.2.2.1, hE.2.2.2,
          nativeSourceSevenEvenBoundaryEnergy, nativeSourceFiveEvenBoundaryEnergy]
      rw [hEzero, zero_add]
      exact mul_pos (by norm_num) (ho _ _ _ _ hO)

/-- A positive eighth source pivot would provide the actual source margin. -/
theorem nativeSourceFiniteBoundaryEnergy_eight_margin_iff :
    (∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin 8 → ℂ,
      ε*‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy 8 x) ↔
      0 < nativeSourceEightOddDiscriminant := by
  rw [← ChiralReturn.nativeSourceFiniteBoundaryEnergy_pos_iff_margin,
    nativeSourceFiniteBoundaryEnergy_eight_pos_iff]

/-- No new sign theorem is presumed: this implication names exactly the
scalar needed to extend the positive physical port from seven to eight. -/
theorem radialReturnTransfer_eight_eventually_contractive_of_oddDiscriminant
    (hd : 0 < nativeSourceEightOddDiscriminant) :
    ∀ᶠ k : ℕ in atTop, ‖ChiralReturn.radialReturnTransfer k 8‖ ≤ 1 := by
  obtain ⟨ε, hε, hb⟩ := nativeSourceFiniteBoundaryEnergy_eight_margin_iff.mpr hd
  exact ChiralReturn.radialReturnTransfer_even_eventually_norm_le_one_of_boundary_margin
    4 ε hε hb

/-- All-order division-free recurrence of the ORIGINAL derivative coefficients.
This uses the source response product identity, before canonical moments. -/
theorem nativeSourceOddBoundaryCoefficient_characteristic_recurrence (n : ℕ) :
    completedNativeRealEvenCharacteristicCoefficient 0 * nativeSourceOddBoundaryCoefficient n +
      ∑ k ∈ Finset.range n, nativeSourceOddBoundaryCoefficient k *
        completedNativeRealEvenCharacteristicCoefficient (n-k) =
      -(2*((n+1:ℕ):ℝ)*completedNativeRealEvenCharacteristicCoefficient (n+1)) := by
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment]
  have h := primeDepthGeometricMoment_isLogDerivativeMomentSequence n
  change completedNativeRealEvenCharacteristicCoefficient 0 * primeDepthGeometricMoment n +
    ∑ k ∈ Finset.range n, primeDepthGeometricMoment k *
      completedNativeRealEvenCharacteristicCoefficient (n-k) = _ at h
  have hs := congrArg (fun r : ℝ => 2*r) h
  simp only [mul_add, Finset.mul_sum, mul_assoc, mul_neg] at hs ⊢
  rw [mul_left_comm (completedNativeRealEvenCharacteristicCoefficient 0) 2]
  exact hs

/-- The old coefficients' entire convolution, with every term retained. -/
def nativeSourceEightEarlierConvolution : ℝ :=
  ∑ k ∈ Finset.range 7, nativeSourceOddBoundaryCoefficient k *
    completedNativeRealEvenCharacteristicCoefficient (7-k)

/-- Couplings fixed by the four-coordinate odd source form. -/
def nativeSourceEightCouplingCorrection : ℝ :=
  nativeSourceOddBoundaryCoefficient 4 * nativeSourceEightOddCoupling0 -
    nativeSourceOddBoundaryCoefficient 5 * nativeSourceEightOddCoupling1 +
    nativeSourceOddBoundaryCoefficient 6 * nativeSourceEightOddCoupling2

/-- Exact ceiling for the NEXT characteristic coefficient, before any bound
is supplied. This quantity is computed from the earlier source data only. -/
def nativeSourceEightCharacteristicCeiling : ℝ :=
  (completedNativeRealEvenCharacteristicCoefficient 0 * nativeSourceEightCouplingCorrection -
    nativeSourceSixOddDiscriminant * nativeSourceEightEarlierConvolution) /
    (16*nativeSourceSixOddDiscriminant)

/-- The new sign is linear in the new native characteristic coefficient. -/
theorem nativeSourceEightOddDiscriminant_characteristic_identity :
    completedNativeRealEvenCharacteristicCoefficient 0 * nativeSourceEightOddDiscriminant =
      completedNativeRealEvenCharacteristicCoefficient 0 * nativeSourceEightCouplingCorrection -
        nativeSourceSixOddDiscriminant * nativeSourceEightEarlierConvolution -
        16*nativeSourceSixOddDiscriminant*completedNativeRealEvenCharacteristicCoefficient 8 := by
  have h := nativeSourceOddBoundaryCoefficient_characteristic_recurrence 7
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h
  change completedNativeRealEvenCharacteristicCoefficient 0 * nativeSourceOddBoundaryCoefficient 7 +
    nativeSourceEightEarlierConvolution = _ at h
  have hs := congrArg (fun r : ℝ => nativeSourceSixOddDiscriminant*r) h
  unfold nativeSourceEightOddDiscriminant nativeSourceEightCouplingCorrection
  nlinarith [hs]

/-- A precise analytic target: the original eight-source positivity is
equivalent to this strict upper bound, not just to a newly named sign gate. -/
theorem nativeSourceEightOddDiscriminant_pos_iff_characteristic_ceiling :
    0 < nativeSourceEightOddDiscriminant ↔
      completedNativeRealEvenCharacteristicCoefficient 8 < nativeSourceEightCharacteristicCeiling := by
  have hc : 0 < completedNativeRealEvenCharacteristicCoefficient 0 := by
    rw [completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment]
    exact completedNativeXiCosineMoment_pos 0
  have hi := nativeSourceEightOddDiscriminant_characteristic_identity
  unfold nativeSourceEightCharacteristicCeiling
  rw [lt_div_iff₀ (mul_pos (by norm_num) nativeSourceSixOddDiscriminant_pos)]
  constructor <;> intro h <;> nlinarith

end
end CarrySelfAdjointOperator

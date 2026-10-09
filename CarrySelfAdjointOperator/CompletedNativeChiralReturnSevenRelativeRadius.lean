import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenRelativeSpectrum

/-!
# Exact relative spectral radius of the first complete storage correction

The dual cofactor is evaluated in the already-certified odd source form.
No metric, moment sequence, eigenvector fit or new positivity premise is used.
-/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The dual energy of (-c4,c5,-c6), computed in the existing odd sewing
coordinates. This is an analysis of that metric, not a replacement for it. -/
def radialSevenOddCouplingDualEnergy : ℝ :=
  let a := nativeSourceOddBoundaryCoefficient 1
  let b := nativeSourceOddBoundaryCoefficient 2
  let c := nativeSourceOddBoundaryCoefficient 3
  let d := nativeSourceOddBoundaryCoefficient 4
  let e := nativeSourceOddBoundaryCoefficient 5
  let f := nativeSourceOddBoundaryCoefficient 6
  let δ := a*c-b^2
  let v := e-b*d/a
  let w := -f+c*d/a-((b*c-a*d)/δ)*v
  d^2/a + (a/δ)*v^2 + (δ/nativeSourceSixOddDiscriminant)*w^2

/-- The polynomial cofactor is the same positive dual energy. -/
theorem radialSevenOddCouplingCofactor_eq_dual :
    radialSevenOddCouplingCofactor =
      nativeSourceSixOddDiscriminant * radialSevenOddCouplingDualEnergy := by
  have ha := nativeSourceMixedLeadingCoefficients_pos.2.ne'
  have hd := nativeSourceMixedDiscriminants_pos.2.ne'
  have hD := nativeSourceSixOddDiscriminant_pos.ne'
  unfold radialSevenOddCouplingCofactor radialSevenOddCouplingDualEnergy
  dsimp only
  field_simp [ha,hd,hD]
  unfold nativeSourceSixOddDiscriminant
  ring

theorem radialSevenOddCouplingDualEnergy_pos : 0 < radialSevenOddCouplingDualEnergy := by
  have ha := nativeSourceMixedLeadingCoefficients_pos.2
  have hd := nativeSourceMixedDiscriminants_pos.2
  have hD := nativeSourceSixOddDiscriminant_pos
  have hc := nativeSourceOddBoundaryCoefficient_four_pos_from_face
  unfold radialSevenOddCouplingDualEnergy
  dsimp only
  positivity

theorem radialSevenOddCouplingCofactor_pos : 0 < radialSevenOddCouplingCofactor := by
  rw [radialSevenOddCouplingCofactor_eq_dual]
  exact mul_pos nativeSourceSixOddDiscriminant_pos radialSevenOddCouplingDualEnergy_pos

/-- The two nonzero relative eigenvalues are the positive and negative values of this source-derived number. -/
def radialSevenFirstCorrectionRelativeRadius : ℝ :=
  28 * Real.sqrt (nativeSourceFiveEvenDiscriminant * radialSevenOddCouplingCofactor /
    (nativeSourceSevenEvenDiscriminant * nativeSourceSixOddDiscriminant))

theorem radialSevenFirstCorrectionRelativeRadius_pos :
    0 < radialSevenFirstCorrectionRelativeRadius := by
  unfold radialSevenFirstCorrectionRelativeRadius
  have hr := div_pos (mul_pos nativeSourceFiveEvenDiscriminant_pos
    radialSevenOddCouplingCofactor_pos) (mul_pos nativeSourceSevenEvenDiscriminant_pos
      nativeSourceSixOddDiscriminant_pos)
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hr)

theorem radialSevenFirstCorrectionRelativeRadius_sq :
    nativeSourceSevenEvenDiscriminant * nativeSourceSixOddDiscriminant *
      radialSevenFirstCorrectionRelativeRadius^2 =
    784 * nativeSourceFiveEvenDiscriminant * radialSevenOddCouplingCofactor := by
  have hr := div_pos (mul_pos nativeSourceFiveEvenDiscriminant_pos
    radialSevenOddCouplingCofactor_pos) (mul_pos nativeSourceSevenEvenDiscriminant_pos
      nativeSourceSixOddDiscriminant_pos)
  unfold radialSevenFirstCorrectionRelativeRadius
  rw [mul_pow,Real.sq_sqrt hr.le]
  field_simp [nativeSourceSevenEvenDiscriminant_pos.ne',nativeSourceSixOddDiscriminant_pos.ne']
  ring

/-- The COMPLETE relative pencil has exactly these real singular parameters.
The earlier determinant factorization also retains the zero factor of degree 5. -/
theorem radialSevenFirstCorrection_relative_spectrum (t : ℝ) :
    (radialSevenFirstCorrectionMatrix - t • nativeSourceSevenBoundaryMatrix).det = 0 ↔
      t = 0 ∨ t = radialSevenFirstCorrectionRelativeRadius ∨
        t = -radialSevenFirstCorrectionRelativeRadius := by
  have hi : (radialSevenFirstCorrectionMatrix - t • nativeSourceSevenBoundaryMatrix).det = 0 ↔
      t = 0 ∨ 784*nativeSourceFiveEvenDiscriminant*radialSevenOddCouplingCofactor -
        nativeSourceSevenEvenDiscriminant*nativeSourceSixOddDiscriminant*t^2 = 0 := by
    rw [radialSevenFirstCorrection_pencil_det]
    simp [mul_eq_zero]
  rw [hi]
  have hD := mul_pos nativeSourceSevenEvenDiscriminant_pos nativeSourceSixOddDiscriminant_pos
  have hs := radialSevenFirstCorrectionRelativeRadius_sq
  constructor
  · intro ht
    rcases ht with ht | ht
    · exact Or.inl ht
    · have he : (t-radialSevenFirstCorrectionRelativeRadius)*
          (t+radialSevenFirstCorrectionRelativeRadius) = 0 := by nlinarith
      rcases mul_eq_zero.mp he with hp | hm
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  · intro ht
    rcases ht with ht | ht | ht
    · exact Or.inl ht
    · exact Or.inr (by rw [ht]; nlinarith)
    · exact Or.inr (by rw [ht]; nlinarith)
/-- Factored pencil with the five zero modes and both nonzero roots explicit. -/
theorem radialSevenFirstCorrection_relative_pencil_factor (t : ℝ) :
    (radialSevenFirstCorrectionMatrix - t • nativeSourceSevenBoundaryMatrix).det =
      128*nativeSourceSevenEvenDiscriminant*nativeSourceSixOddDiscriminant*t^5 *
        (radialSevenFirstCorrectionRelativeRadius^2-t^2) := by
  rw [radialSevenFirstCorrection_pencil_det]
  linear_combination -128*t^5 * radialSevenFirstCorrectionRelativeRadius_sq
end
end CarrySelfAdjointOperator

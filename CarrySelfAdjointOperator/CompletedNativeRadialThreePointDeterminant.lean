import CarrySelfAdjointOperator.CompletedNativeSixthOrderHankelGate
import CarrySelfAdjointOperator.CompletedNativeChiralTwoPointControl

/-!
# Three-point determinant with the existing radial remainder control

The normalized three-point finite-difference matrix is a congruence of the
existing native sample matrix. The previously proved radial coefficient
limits control its determinant, including the remainder. In particular,
division of the original determinant by the sixth power of the radial step
converges to `4 h₁ (h₀ h₂ - h₁²)`.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace CarrySelfAdjointOperator

open Filter
noncomputable section
set_option autoImplicit false

/-- Three columns of the existing normalized forward-difference stencil.
This is a coordinate change on three samples, not a new kernel. -/
def completedGreenThreePointDifferenceTransform (h : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, -h⁻¹, (2*h^2)⁻¹;
     0, h⁻¹, -(h^2)⁻¹;
     0, 0, (2*h^2)⁻¹]

/-- Literal congruence for the three normalized mixed differences. -/
theorem completedGreenThreePointDifference_congruence
    (kernel : ℂ → ℂ → ℂ) (h : ℂ) (hh : h ≠ 0) :
    (Matrix.of fun p q : Fin 3 =>
      completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
      Matrix.conjTranspose (completedGreenThreePointDifferenceTransform h) *
        (Matrix.of fun i j : Fin 3 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) *
        completedGreenThreePointDifferenceTransform h := by
  have hc : conj h ≠ 0 := by simpa using hh
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [completedGreenThreePointDifferenceTransform,
      completedGreenKernelTwoStepShiftedForwardDifference,
      completedGreenKernelTwoStepShiftedRawDifference,
      Function.iterate_succ_apply, completedGreenForwardDifference,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      two_mul, add_assoc] <;>
    field_simp [hh, hc] <;> ring

/-- Determinant of this exact stencil, including the second factorial. -/
theorem completedGreenThreePointDifferenceTransform_det (h : ℂ) :
    (completedGreenThreePointDifferenceTransform h).det = (2*h^3)⁻¹ := by
  rw [Matrix.det_fin_three]
  simp [completedGreenThreePointDifferenceTransform, mul_inv_rev, pow_succ, mul_assoc]

/-- The normalized differences of the native kernel on the three existing
radial points. Its limit already has a proved all-order remainder control. -/
def canonicalCompletedNativeRadialThreePointDifferenceMatrix (k : ℕ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun p q => completedGreenKernelTwoStepShiftedForwardDifference
    canonicalCompletedNativePolarizedDslopeKernel
    (canonicalCompletedC3RadialSecondStep k)
    (canonicalCompletedC3RadialSecondStep k) p q

/-- The coordinate change acts on precisely the existing native samples. -/
theorem canonicalCompletedNativeRadialThreePointDifferenceMatrix_eq_congruence (k : ℕ) :
    canonicalCompletedNativeRadialThreePointDifferenceMatrix k =
      Matrix.conjTranspose (completedGreenThreePointDifferenceTransform (canonicalCompletedC3RadialSecondStep k)) *
        canonicalCompletedNativeRadialDslopeSampleMatrix k 3 *
        completedGreenThreePointDifferenceTransform (canonicalCompletedC3RadialSecondStep k) := by
  rw [canonicalCompletedNativeRadialThreePointDifferenceMatrix,
    completedGreenThreePointDifference_congruence _ _
      (canonicalCompletedC3RadialSecondStep_ne_zero k)]
  congr 2
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [nsmul_eq_mul]

/-- The confluent three-point determinant is the first shifted moment times
the ordinary second Hankel determinant. -/
theorem polarizedGreenMomentCoefficient_three_det (h : ℕ → ℝ) :
    (Matrix.of fun i j : Fin 3 => polarizedGreenMomentCoefficient h i j).det =
      ((h 1 * (h 0 * h 2 - h 1^2) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_three]
  norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]
  ring

/-- Reuse the shifted radial coefficient limits, including their analytic
remainders, for this actual finite-difference matrix. -/
theorem canonicalCompletedNativeRadialThreePointDifferenceMatrix_tendsto :
    Tendsto canonicalCompletedNativeRadialThreePointDifferenceMatrix atTop
      (nhds (Matrix.of fun i j : Fin 3 =>
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment i j)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hd : Tendsto (fun k : ℕ => (k,k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  change Tendsto (fun k => completedGreenKernelTwoStepShiftedForwardDifference
    canonicalCompletedNativePolarizedDslopeKernel
    (canonicalCompletedC3RadialSecondStep k) (canonicalCompletedC3RadialSecondStep k)
    (i : ℕ) (j : ℕ)) atTop (nhds _)
  simpa only [Function.comp_def, Matrix.of_apply] using
    (completedNativePolarizedDslope_shiftedRadial_tendsto (i : ℕ) (j : ℕ)).comp hd

/-- The limiting normalized determinant is exactly `h₁ Δ₂`. -/
theorem canonicalCompletedNativeRadialThreePointDifferenceMatrix_det_tendsto :
    Tendsto (fun k => (canonicalCompletedNativeRadialThreePointDifferenceMatrix k).det) atTop
      (nhds ((canonicalCompletedNativeLogDerivativeMoment 1 *
        (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det : ℝ) : ℂ)) := by
  have h := (continuous_id.matrix_det.tendsto _).comp
    canonicalCompletedNativeRadialThreePointDifferenceMatrix_tendsto
  simpa only [Function.comp_def, id_eq, polarizedGreenMomentCoefficient_three_det,
    canonicalCompletedNativeHankel_two_det_eq] using h

/-- The determinant scale is exactly `4 ε⁶`. The factor four is the square
of the second factorial, and the sixth power comes from the two stencils. -/
theorem canonicalCompletedNativeRadialThreePointDifferenceMatrix_det_eq (k : ℕ) :
    (canonicalCompletedNativeRadialThreePointDifferenceMatrix k).det =
      (canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det /
        (4 * (canonicalGreenJetRealStep k : ℂ)^6) := by
  rw [canonicalCompletedNativeRadialThreePointDifferenceMatrix_eq_congruence,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    completedGreenThreePointDifferenceTransform_det]
  have hs : canonicalCompletedC3RadialSecondStep k =
      Complex.I * (canonicalGreenJetRealStep k : ℂ) := by
    simp [canonicalCompletedC3RadialSecondStep, canonicalGreenJetStep,
      canonicalGreenJetRealStep]
  have hp : 0 < canonicalGreenJetRealStep k := by
    unfold canonicalGreenJetRealStep
    positivity
  have hc : (canonicalGreenJetRealStep k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  rw [hs]
  simp only [Complex.star_def, map_inv₀, map_mul, map_pow, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal]
  field_simp [hc]
  ring_nf
  have hI : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2)^3 := by ring
      _ = -1 := by rw [Complex.I_sq]; norm_num
  rw [hI]
  ring

/-- Main remainder-controlled asymptotic along the existing canonical
steps `εₖ=1/(k+1)`. Lower orders vanish and the normalized limit is the
coefficient computed by the rational polynomial diagnostic. -/
theorem canonicalCompletedNativeRadialThreePointDeterminant_div_sixthStep_tendsto :
    Tendsto (fun k : ℕ =>
      (canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det /
        (canonicalGreenJetRealStep k : ℂ)^6) atTop
      (nhds ((4 * canonicalCompletedNativeLogDerivativeMoment 1 *
        (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det : ℝ) : ℂ)) := by
  have h := canonicalCompletedNativeRadialThreePointDifferenceMatrix_det_tendsto.const_mul (4:ℂ)
  convert h using 1
  · funext k
    rw [canonicalCompletedNativeRadialThreePointDifferenceMatrix_det_eq]
    ring_nf
  · push_cast
    ring

/-- Strict positivity of the new scalar makes the real determinant positive
on sufficiently small radial steps. The scalar is explicit in the premise;
this theorem does not supply its still-missing native analytic proof. -/
theorem canonicalCompletedNativeRadialThreePointDeterminant_eventually_re_pos_of_delta
    (hdelta : 0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det) :
    ∀ᶠ k : ℕ in atTop,
      0 < (canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det.re := by
  have h₁ := (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive).2
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    canonicalCompletedNativeRadialThreePointDeterminant_div_sixthStep_tendsto
  have he : ∀ᶠ k : ℕ in atTop,
      0 < ((canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det /
        (canonicalGreenJetRealStep k : ℂ)^6).re := by
    apply Filter.Tendsto.eventually_lt tendsto_const_nhds h
    simpa only [Complex.ofReal_re] using
      mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) h₁) hdelta
  filter_upwards [he] with k hk
  have hs : 0 < canonicalGreenJetRealStep k ^ 6 := by
    unfold canonicalGreenJetRealStep
    positivity
  have hk' : 0 < (canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det.re /
      canonicalGreenJetRealStep k ^ 6 := by
    simpa only [← Complex.ofReal_pow, Complex.div_ofReal_re] using hk
  exact (div_pos_iff_of_pos_right hs).mp hk'

end
end CarrySelfAdjointOperator

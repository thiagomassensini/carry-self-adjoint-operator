import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralCarrier
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# Central chiral quotient and second-order curvature

The projective/chiral route replaces the incorrectly normalized raw ambient
Gram by the exact Hermite--Biehler quotient

`q = (-F' - iF) / (-F' + iF)`.

At the centered height, evenness gives `F'(0) = 0` and hence `q(0) = -1`.
The first variation of `q` therefore starts with the second derivative of
`F`: it is exactly `-4 i` times the zeroth completed-native logarithmic
moment.  On the transverse real parameter `z = i y`, the quarter turn removes
the `i`, so the first radial variation is `4 h₀`.

This identifies the first local Pick coefficient with the already formalized
central curvature.  It does not assert the all-order Pick positivity or
multiplier contractivity required by the completed Hankel gate.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

private theorem hasDerivAt_completedNativeOperatorCharacteristic_deriv_zero :
    HasDerivAt (deriv completedNativeOperatorCharacteristic)
      (iteratedDeriv 2 completedNativeOperatorCharacteristic 0) 0 := by
  have h :=
    (completedNativeOperatorCharacteristic_analyticAt
      zero_mem_completedNativeHeightDomain).deriv.differentiableAt.hasDerivAt
  simpa [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ] using h

/-- Both Hermite--Biehler coordinates have the same first derivative at the
center because the value channel is stationary there. -/
theorem hasDerivAt_completedNativePositiveHermiteBiehlerCoordinate_zero :
    HasDerivAt completedNativePositiveHermiteBiehlerCoordinate
      (-iteratedDeriv 2 completedNativeOperatorCharacteristic 0) 0 := by
  have hF :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.hasDerivAt
  have hFzero : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  have h :=
    hasDerivAt_completedNativeOperatorCharacteristic_deriv_zero.neg.add
      (hF.const_mul Complex.I)
  change HasDerivAt
    (fun z => -deriv completedNativeOperatorCharacteristic z +
      Complex.I * completedNativeOperatorCharacteristic z)
    (-iteratedDeriv 2 completedNativeOperatorCharacteristic 0) 0
  convert h using 1 <;> first | rfl | simp [hFzero]

theorem hasDerivAt_completedNativeNegativeHermiteBiehlerCoordinate_zero :
    HasDerivAt completedNativeNegativeHermiteBiehlerCoordinate
      (-iteratedDeriv 2 completedNativeOperatorCharacteristic 0) 0 := by
  have hF :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.hasDerivAt
  have hFzero : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  have h :=
    hasDerivAt_completedNativeOperatorCharacteristic_deriv_zero.neg.sub
      (hF.const_mul Complex.I)
  change HasDerivAt
    (fun z => -deriv completedNativeOperatorCharacteristic z -
      Complex.I * completedNativeOperatorCharacteristic z)
    (-iteratedDeriv 2 completedNativeOperatorCharacteristic 0) 0
  convert h using 1 <;> first | rfl | simp [hFzero]

/-- First-order chiral quotient formula before rewriting the characteristic
curvature as the canonical moment. -/
theorem hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero_raw :
    HasDerivAt completedNativeHermiteBiehlerChiralQuotient
      (2 * Complex.I * iteratedDeriv 2 completedNativeOperatorCharacteristic 0 /
        completedNativeOperatorCharacteristic 0) 0 := by
  have hden : completedNativePositiveHermiteBiehlerCoordinate 0 ≠ 0 := by
    rw [completedNativePositiveHermiteBiehlerCoordinate_zero]
    exact mul_ne_zero Complex.I_ne_zero
      completedNativeOperatorCharacteristic_zero_ne_zero
  have h :=
    hasDerivAt_completedNativeNegativeHermiteBiehlerCoordinate_zero.div
      hasDerivAt_completedNativePositiveHermiteBiehlerCoordinate_zero hden
  have hcoefficient :
      ((-iteratedDeriv 2 completedNativeOperatorCharacteristic 0) *
            completedNativePositiveHermiteBiehlerCoordinate 0 -
          completedNativeNegativeHermiteBiehlerCoordinate 0 *
            (-iteratedDeriv 2 completedNativeOperatorCharacteristic 0)) /
          completedNativePositiveHermiteBiehlerCoordinate 0 ^ 2 =
        2 * Complex.I *
            iteratedDeriv 2 completedNativeOperatorCharacteristic 0 /
          completedNativeOperatorCharacteristic 0 := by
    rw [completedNativePositiveHermiteBiehlerCoordinate_zero,
      completedNativeNegativeHermiteBiehlerCoordinate_zero]
    have hF := completedNativeOperatorCharacteristic_zero_ne_zero
    field_simp [hF, Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring
  rw [hcoefficient] at h
  change HasDerivAt
    (fun z => completedNativeNegativeHermiteBiehlerCoordinate z /
      completedNativePositiveHermiteBiehlerCoordinate z)
    (2 * Complex.I * iteratedDeriv 2 completedNativeOperatorCharacteristic 0 /
      completedNativeOperatorCharacteristic 0) 0
  convert h using 1 <;> rfl

/-- Public curvature spelling used by the chiral quotient audit. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      -iteratedDeriv 2 completedNativeOperatorCharacteristic 0 /
        (2 * completedNativeOperatorCharacteristic 0) := by
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_productJet,
    ← completedNativeOperatorCharacteristic_secondDerivative_product]
  simp only [completedNativeOperatorCharacteristic, nativeHeightScalar]
  ring

/-- The first complex variation of the chiral quotient is the second-order
completed curvature, equivalently `-4 i h₀`. -/
theorem hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero :
    HasDerivAt completedNativeHermiteBiehlerChiralQuotient
      (-4 * Complex.I *
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) 0 := by
  have hraw :=
    hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero_raw
  have hm :=
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral
  rw [hm]
  convert hraw using 1
  have hF := completedNativeOperatorCharacteristic_zero_ne_zero
  field_simp [hF]
  ring

/-- Chiral quotient restricted to the transverse centered line `z = i y`. -/
def completedNativeCentralHermiteBiehlerChiralQuotient (y : ℝ) : ℂ :=
  completedNativeHermiteBiehlerChiralQuotient
    (Complex.I * (y : ℂ))

@[simp] theorem completedNativeCentralHermiteBiehlerChiralQuotient_zero :
    completedNativeCentralHermiteBiehlerChiralQuotient 0 = -1 := by
  simp [completedNativeCentralHermiteBiehlerChiralQuotient]

/-- On the transverse real parameter, the two quarter turns cancel and the
first variation is the real scalar `4 h₀`. -/
theorem hasDerivAt_completedNativeCentralHermiteBiehlerChiralQuotient_zero :
    HasDerivAt completedNativeCentralHermiteBiehlerChiralQuotient
      (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) 0 := by
  have hline : HasDerivAt (fun u : ℂ => Complex.I * u) Complex.I 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul Complex.I
  have houter : HasDerivAt completedNativeHermiteBiehlerChiralQuotient
      (-4 * Complex.I *
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))
      ((fun u : ℂ => Complex.I * u) 0) := by
    simpa using hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero
  have hcomplex : HasDerivAt
      (fun u : ℂ => completedNativeHermiteBiehlerChiralQuotient
        (Complex.I * u))
      ((-4 * Complex.I *
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) * Complex.I) 0 :=
    houter.comp (𝕜 := ℂ) (𝕜' := ℂ) 0 hline
  have hreal := hcomplex.comp_ofReal
  have hcoefficient :
      (-4 * Complex.I *
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) * Complex.I =
        4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
    rw [show -4 * Complex.I *
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) * Complex.I =
      -4 * (Complex.I * Complex.I) *
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) by ring,
      Complex.I_mul_I]
    ring
  rw [hcoefficient] at hreal
  change HasDerivAt
    (fun y : ℝ => completedNativeHermiteBiehlerChiralQuotient
      (Complex.I * (y : ℂ)))
    (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) 0
  convert hreal using 1

/-- Real defect of the chiral multiplier norm on the centered transverse
line.  It vanishes at the center because `q(0) = -1`. -/
def completedNativeCentralChiralQuotientNormDefect (y : ℝ) : ℝ :=
  1 - ‖completedNativeCentralHermiteBiehlerChiralQuotient y‖ ^ 2

@[simp] theorem completedNativeCentralChiralQuotientNormDefect_zero :
    completedNativeCentralChiralQuotientNormDefect 0 = 0 := by
  simp [completedNativeCentralChiralQuotientNormDefect]

/-- The first norm-defect variation is `8 h₀`.  Thus the diagonal Pick
quotient, which divides this defect by `2y`, has removable value `4 h₀`. -/
theorem hasDerivAt_completedNativeCentralChiralQuotientNormDefect_zero :
    HasDerivAt completedNativeCentralChiralQuotientNormDefect
      (8 * canonicalCompletedNativeLogDerivativeMoment 0) 0 := by
  have hnorm :=
    hasDerivAt_completedNativeCentralHermiteBiehlerChiralQuotient_zero.norm_sq
  have hreal :
      (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) =
        ((4 * canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hreal] at hnorm
  have h := (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hnorm
  change HasDerivAt
    (fun y => 1 -
      ‖completedNativeCentralHermiteBiehlerChiralQuotient y‖ ^ 2)
    (8 * canonicalCompletedNativeLogDerivativeMoment 0) 0
  convert h using 1 <;> first
    | rfl
    | (simp [completedNativeCentralHermiteBiehlerChiralQuotient_zero,
        real_inner_eq_re_inner, RCLike.inner_apply]; ring)

/-- The punctured diagonal Pick scalar has the central value `4 h₀`. -/
theorem completedNativeCentralChiralQuotientNormDefect_div_tendsto_four_moment_zero :
    Filter.Tendsto
      (fun y : ℝ =>
        completedNativeCentralChiralQuotientNormDefect y / (2 * y))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (4 * canonicalCompletedNativeLogDerivativeMoment 0)) := by
  have hslope :=
    (hasDerivAt_iff_tendsto_slope_zero.mp
      hasDerivAt_completedNativeCentralChiralQuotientNormDefect_zero)
  have hscaled : Filter.Tendsto
      (fun y : ℝ => (2 : ℝ)⁻¹ *
        (y⁻¹ •
          (completedNativeCentralChiralQuotientNormDefect (0 + y) -
            completedNativeCentralChiralQuotientNormDefect 0)))
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((2 : ℝ)⁻¹ *
        (8 * canonicalCompletedNativeLogDerivativeMoment 0))) :=
    tendsto_const_nhds.mul hslope
  have htarget :
      (2 : ℝ)⁻¹ * (8 * canonicalCompletedNativeLogDerivativeMoment 0) =
        4 * canonicalCompletedNativeLogDerivativeMoment 0 := by ring
  rw [htarget] at hscaled
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyne : y ≠ 0 := by simpa using hy
  simp only [completedNativeCentralChiralQuotientNormDefect_zero,
    zero_add, sub_zero, smul_eq_mul]
  field_simp [hyne]

/-! ## Diagonal Pick-kernel readout -/

/-- Away from the removable central singularity, the diagonal chiral Pick
kernel is exactly the real norm defect divided by the upper-half-plane
separation `2y`. -/
theorem completedNativeHermiteBiehlerChiralPickKernel_central_diagonal
    {y : ℝ} (hy : y ≠ 0) :
    completedNativeHermiteBiehlerChiralPickKernel
        (Complex.I * (y : ℂ)) (Complex.I * (y : ℂ)) =
      (completedNativeCentralChiralQuotientNormDefect y / (2 * y) : ℝ) := by
  unfold completedNativeHermiteBiehlerChiralPickKernel
    completedNativeCentralChiralQuotientNormDefect
    completedNativeCentralHermiteBiehlerChiralQuotient
  rw [RCLike.conj_mul]
  have hyComplex : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  push_cast
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  field_simp [hyComplex, Complex.I_ne_zero]
  ring_nf
  norm_num

/-- The diagonal Pick kernel has removable central value `4 h₀`.  This is
the one-point/first-order shadow of the all-order radial Pick positivity (or,
equivalently, chiral multiplier contractivity) gate. -/
theorem completedNativeHermiteBiehlerChiralPickKernel_central_diagonal_tendsto :
    Filter.Tendsto
      (fun y : ℝ =>
        completedNativeHermiteBiehlerChiralPickKernel
          (Complex.I * (y : ℂ)) (Complex.I * (y : ℂ)))
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((4 * canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ)) := by
  have h := Filter.tendsto_ofReal_iff.mpr
    completedNativeCentralChiralQuotientNormDefect_div_tendsto_four_moment_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (completedNativeHermiteBiehlerChiralPickKernel_central_diagonal
    (by simpa using hy)).symm

/-- Every canonical radial sample lies on the same centered transverse line,
with its imaginary part as real parameter. -/
theorem canonicalCompletedC3RadialTiltPoint_eq_I_mul_im
    (k n : ℕ) :
    canonicalCompletedC3RadialTiltPoint k n =
      Complex.I *
        ((canonicalCompletedC3RadialTiltPoint k n).im : ℂ) := by
  rw [canonicalCompletedC3RadialTiltPoint_im]
  unfold canonicalCompletedC3RadialTiltPoint
    canonicalCompletedC3RadialTiltStep
  rw [← canonicalGreenJetRealStep_coe]
  unfold canonicalGreenJetRealStep
  push_cast
  ring

/-- Strict positivity of the central moment closes the first (`N = 1`)
radial multiplier section eventually.  The higher finite sections still
contain genuinely polarized off-diagonal conditions. -/
theorem
    canonicalCompletedNativeRadialChiralMultiplierContractiveAt_one_eventually_of_moment_zero_pos
    (hmoment : 0 < canonicalCompletedNativeLogDerivativeMoment 0) :
    ∀ᶠ k : ℕ in Filter.atTop,
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k 1 := by
  let height : ℕ → ℝ := fun k =>
    (canonicalCompletedC3RadialTiltPoint k 0).im
  have hheight : Filter.Tendsto height Filter.atTop (nhds 0) := by
    have him := (Complex.continuous_im.tendsto 0).comp
      (canonicalCompletedC3RadialTiltPoint_tendsto_zero 0)
    change Filter.Tendsto
      (fun k => (canonicalCompletedC3RadialTiltPoint k 0).im)
      Filter.atTop (nhds 0) at him
    exact him
  have hheightNonzero : ∀ᶠ k : ℕ in Filter.atTop,
      height k ∈ ({0} : Set ℝ)ᶜ := by
    filter_upwards [] with k
    simpa [height] using
      canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0
  have hheightWithin :
      Filter.Tendsto height Filter.atTop
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hheight, hheightNonzero⟩
  have hquotient :=
    completedNativeCentralChiralQuotientNormDefect_div_tendsto_four_moment_zero.comp
      hheightWithin
  have hpositive : ∀ᶠ k : ℕ in Filter.atTop,
      0 < completedNativeCentralChiralQuotientNormDefect (height k) /
        (2 * height k) :=
    Filter.Tendsto.eventually_lt tendsto_const_nhds hquotient
      (by positivity)
  filter_upwards [hpositive] with k hk
  apply
    (canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
      k 1).mpr
  have hmatrix :
      canonicalCompletedNativeRadialChiralPickSampleMatrix k 1 =
        Matrix.diagonal (fun _ : Fin 1 =>
          ((completedNativeCentralChiralQuotientNormDefect (height k) /
            (2 * height k) : ℝ) : ℂ)) := by
    ext i j
    fin_cases i
    fin_cases j
    unfold canonicalCompletedNativeRadialChiralPickSampleMatrix
    simp only [Matrix.of_apply, Matrix.diagonal_apply_eq]
    rw [canonicalCompletedC3RadialTiltPoint_eq_I_mul_im,
      completedNativeHermiteBiehlerChiralPickKernel_central_diagonal
        (by simpa [height] using
          canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)]
  rw [hmatrix, Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast hk.le

/-! ## The centered `1/4 × 4` normalization -/

/-- The normalized positive chiral Gram tends to its exact centered energy
`1/4` along the same punctured transverse line. -/
theorem
    completedNativeNormalizedPositiveChiralTraceKernel_central_diagonal_tendsto_quarter :
    Filter.Tendsto
      (fun y : ℝ =>
        completedNativeNormalizedPositiveChiralTraceKernel
          (Complex.I * (y : ℂ)) (Complex.I * (y : ℂ)))
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((1 / 4 : ℝ) : ℂ)) := by
  let point : ℝ → ℂ := fun y => Complex.I * (y : ℂ)
  have hpoint : Filter.Tendsto point (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hcontinuous : ContinuousAt point 0 := by
      fun_prop
    simpa [point] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hFanalytic :=
    completedNativeOperatorCharacteristic_analyticAt
      zero_mem_completedNativeHeightDomain
  have hpositiveContinuous :
      ContinuousAt completedNativePositiveHermiteBiehlerCoordinate 0 := by
    unfold completedNativePositiveHermiteBiehlerCoordinate
    exact hFanalytic.deriv.neg.continuousAt.add
      (continuousAt_const.mul hFanalytic.continuousAt)
  have hpositive := hpositiveContinuous.tendsto.comp hpoint
  have hF := hFanalytic.continuousAt.tendsto.comp hpoint
  have hden :
      4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2 ≠ 0 := by
    have hnorm : ‖completedNativeOperatorCharacteristic 0‖ ≠ 0 :=
      norm_ne_zero_iff.mpr
        completedNativeOperatorCharacteristic_zero_ne_zero
    positivity
  have hquotient : Filter.Tendsto
      (fun y : ℝ =>
        ‖completedNativePositiveHermiteBiehlerCoordinate (point y)‖ ^ 2 /
          (4 * ‖completedNativeOperatorCharacteristic (point y)‖ ^ 2))
      (nhdsWithin 0 {0}ᶜ)
      (nhds
        (‖completedNativePositiveHermiteBiehlerCoordinate 0‖ ^ 2 /
          (4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2))) :=
    (hpositive.norm.pow 2).div
      (tendsto_const_nhds.mul (hF.norm.pow 2)) hden
  have htarget :
      ‖completedNativePositiveHermiteBiehlerCoordinate 0‖ ^ 2 /
          (4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2) =
        (1 / 4 : ℝ) := by
    rw [completedNativePositiveHermiteBiehlerCoordinate_zero,
      norm_mul, Complex.norm_I, one_mul]
    have hnorm : ‖completedNativeOperatorCharacteristic 0‖ ≠ 0 :=
      norm_ne_zero_iff.mpr
        completedNativeOperatorCharacteristic_zero_ne_zero
    field_simp [hnorm]
  rw [htarget] at hquotient
  have hcomplex := Filter.tendsto_ofReal_iff.mpr hquotient
  apply hcomplex.congr'
  have hnonzero : ∀ᶠ y : ℝ in nhdsWithin 0 {0}ᶜ,
      completedNativeOperatorCharacteristic (point y) ≠ 0 :=
    hpoint.eventually
      (hFanalytic.continuousAt.eventually_ne
        completedNativeOperatorCharacteristic_zero_ne_zero)
  filter_upwards [hnonzero] with y hyF
  have hyF' : completedNativeOperatorCharacteristic
      (Complex.I * (y : ℂ)) ≠ 0 := by
    simpa [point] using hyF
  rw [show point y = Complex.I * (y : ℂ) by rfl]
  unfold completedNativeNormalizedPositiveChiralTraceKernel
  rw [inner_self_eq_norm_sq_to_K]
  rw [← RCLike.ofReal_pow]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (norm_sq_completedNativeNormalizedPositiveChiralTraceState hyF').symm

/-- The central positive-channel factor `1/4` cancels the Pick coefficient
`4 h₀`, leaving exactly the zeroth completed-native moment.  This is the
precise theorem behind the recurring quarter/four normalization. -/
theorem completedNativeCentralPositiveChiralPickProduct_tendsto_moment_zero :
    Filter.Tendsto
      (fun y : ℝ =>
        completedNativeNormalizedPositiveChiralTraceKernel
            (Complex.I * (y : ℂ)) (Complex.I * (y : ℂ)) *
          completedNativeHermiteBiehlerChiralPickKernel
            (Complex.I * (y : ℂ)) (Complex.I * (y : ℂ)))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  have hproduct :=
    completedNativeNormalizedPositiveChiralTraceKernel_central_diagonal_tendsto_quarter.mul
      completedNativeHermiteBiehlerChiralPickKernel_central_diagonal_tendsto
  convert hproduct using 1
  push_cast
  norm_num
  ring

end

end CarrySelfAdjointOperator

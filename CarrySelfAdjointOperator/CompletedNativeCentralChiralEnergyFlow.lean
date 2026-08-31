import CarrySelfAdjointOperator.CompletedNativeChiralHankelDominance
import CarrySelfAdjointOperator.CompletedNativeCentralCarryAtlasEnergy
import CarrySelfAdjointOperator.CompletedC3AmbientRadialTiltSamplePositivity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

/-!
# Central chiral energy flow audit

The center-pinned chiral kernels and the diagonal chiral energies are distinct
objects.  The former have constant sum when one endpoint is fixed at the
Taylor center.  The latter obey a Pythagorean identity with a nonnegative
log-jet contribution and need not be constant away from the center.

This module records that distinction and compares the exact signed chiral
first variation with the independently positive C3 Green-bulk variation.  No
equality between those two variations is assumed.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Diagonal energy versus center-pinned overlap -/

/-- Sum of the two normalized scalar chiral energies at one spectral point. -/
def completedNativeNormalizedChiralTraceTotalEnergy (z : ℂ) : ℝ :=
  ‖completedNativeNormalizedPositiveChiralTraceState z‖ ^ 2 +
    ‖completedNativeNormalizedNegativeChiralTraceState z‖ ^ 2

/-- Exact Pythagorean formula for the diagonal chiral energy.  Besides the
constant value channel `1 / 2`, it retains the nonnegative normalized log-jet
energy. -/
theorem completedNativeNormalizedChiralTraceTotalEnergy_eq
    {z : ℂ} (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeNormalizedChiralTraceTotalEnergy z =
      (1 : ℝ) / 2 +
        ‖deriv completedNativeOperatorCharacteristic z‖ ^ 2 /
          (2 * ‖completedNativeOperatorCharacteristic z‖ ^ 2) := by
  unfold completedNativeNormalizedChiralTraceTotalEnergy
  rw [norm_sq_completedNativeNormalizedPositiveChiralTraceState hzF,
    norm_sq_completedNativeNormalizedNegativeChiralTraceState hzF]
  have hparallelogram := parallelogram_law_with_norm (𝕜 := ℂ)
    (-deriv completedNativeOperatorCharacteristic z)
    (Complex.I * completedNativeOperatorCharacteristic z)
  have hcoordinate :
      ‖completedNativePositiveHermiteBiehlerCoordinate z‖ ^ 2 +
          ‖completedNativeNegativeHermiteBiehlerCoordinate z‖ ^ 2 =
        2 * (‖deriv completedNativeOperatorCharacteristic z‖ ^ 2 +
          ‖completedNativeOperatorCharacteristic z‖ ^ 2) := by
    simpa [completedNativePositiveHermiteBiehlerCoordinate,
      completedNativeNegativeHermiteBiehlerCoordinate, norm_neg, norm_mul,
      Complex.norm_I] using hparallelogram
  have hnorm : ‖completedNativeOperatorCharacteristic z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hzF
  rw [← add_div]
  rw [hcoordinate]
  field_simp [hnorm]
  ring

/-- The diagonal total energy is bounded below by its centered value. -/
theorem completedNativeNormalizedChiralTraceTotalEnergy_ge_half
    {z : ℂ} (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    (1 : ℝ) / 2 ≤ completedNativeNormalizedChiralTraceTotalEnergy z := by
  rw [completedNativeNormalizedChiralTraceTotalEnergy_eq hzF]
  have hden : 0 ≤ 2 * ‖completedNativeOperatorCharacteristic z‖ ^ 2 := by
    positivity
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hden)

/-- The exact centered diagonal energy agrees with the previously proved two
quarter-energy decomposition. -/
@[simp] theorem completedNativeNormalizedChiralTraceTotalEnergy_zero :
    completedNativeNormalizedChiralTraceTotalEnergy 0 = (1 : ℝ) / 2 := by
  exact completedNativeNormalizedChiralTrace_totalEnergy_zero

/-- The center is a local minimum of the diagonal total energy.  This is the
valid conservation statement supplied by the quadratic norm: stationarity at
the center, not constancy of the diagonal energy germ. -/
theorem completedNativeNormalizedChiralTraceTotalEnergy_isLocalMin_zero :
    IsLocalMin completedNativeNormalizedChiralTraceTotalEnergy 0 := by
  have hnonzero : ∀ᶠ z in nhds (0 : ℂ),
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hnonzero] with z hzF
  rw [completedNativeNormalizedChiralTraceTotalEnergy_zero]
  exact completedNativeNormalizedChiralTraceTotalEnergy_ge_half hzF

/-- Diagonal total energy restricted to the transverse centered line. -/
def completedNativeCentralChiralTotalEnergy (y : ℝ) : ℝ :=
  completedNativeNormalizedChiralTraceTotalEnergy
    (Complex.I * (y : ℂ))

/-- Positive diagonal chiral energy on the transverse centered line. -/
def completedNativeCentralPositiveChiralEnergy (y : ℝ) : ℝ :=
  ‖completedNativeNormalizedPositiveChiralTraceState
      (Complex.I * (y : ℂ))‖ ^ 2

/-- Negative diagonal chiral energy on the same line. -/
def completedNativeCentralNegativeChiralEnergy (y : ℝ) : ℝ :=
  ‖completedNativeNormalizedNegativeChiralTraceState
      (Complex.I * (y : ℂ))‖ ^ 2

theorem completedNativeCentralChiralTotalEnergy_eq_add (y : ℝ) :
    completedNativeCentralChiralTotalEnergy y =
      completedNativeCentralPositiveChiralEnergy y +
        completedNativeCentralNegativeChiralEnergy y := by
  rfl

theorem completedNativeCentralChiralEnergyDifference_eq_sub (y : ℝ) :
    completedNativeCentralChiralEnergyDifference y =
      completedNativeCentralPositiveChiralEnergy y -
        completedNativeCentralNegativeChiralEnergy y := by
  rfl

@[simp] theorem completedNativeCentralChiralTotalEnergy_zero :
    completedNativeCentralChiralTotalEnergy 0 = (1 : ℝ) / 2 := by
  simp [completedNativeCentralChiralTotalEnergy]

/-- The centered minimum persists after restriction to the real tilt line. -/
theorem completedNativeCentralChiralTotalEnergy_isLocalMin_zero :
    IsLocalMin completedNativeCentralChiralTotalEnergy 0 := by
  have hpoint : Filter.Tendsto (fun y : ℝ => Complex.I * (y : ℂ))
      (nhds 0) (nhds 0) := by
    have hcontinuous : ContinuousAt
        (fun y : ℝ => Complex.I * (y : ℂ)) 0 := by
      fun_prop
    simpa using hcontinuous.tendsto
  have hnonzero : ∀ᶠ y : ℝ in nhds 0,
      completedNativeOperatorCharacteristic
        (Complex.I * (y : ℂ)) ≠ 0 := by
    exact hpoint.eventually
      (completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
        completedNativeOperatorCharacteristic_zero_ne_zero)
  filter_upwards [hnonzero] with y hyF
  rw [completedNativeCentralChiralTotalEnergy_zero]
  exact completedNativeNormalizedChiralTraceTotalEnergy_ge_half hyF

/-- Fermat stationarity of the full diagonal chiral energy at the center. -/
theorem deriv_completedNativeCentralChiralTotalEnergy_zero :
    deriv completedNativeCentralChiralTotalEnergy 0 = 0 := by
  exact completedNativeCentralChiralTotalEnergy_isLocalMin_zero.deriv_eq_zero

/-- The diagonal total energy is genuinely differentiable at the center. -/
theorem completedNativeCentralChiralTotalEnergy_differentiableAt_zero :
    DifferentiableAt ℝ completedNativeCentralChiralTotalEnergy 0 := by
  let line : ℝ → ℂ := fun y => Complex.I * (y : ℂ)
  let model : ℝ → ℝ := fun y =>
    (1 : ℝ) / 2 +
      ‖deriv completedNativeOperatorCharacteristic (line y)‖ ^ 2 /
        (2 * ‖completedNativeOperatorCharacteristic (line y)‖ ^ 2)
  have hlineComplex : HasDerivAt (fun u : ℂ => Complex.I * u)
      Complex.I 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul Complex.I
  have hFline : DifferentiableAt ℝ
      (fun y : ℝ => completedNativeOperatorCharacteristic (line y)) 0 := by
    have hFderiv : HasDerivAt completedNativeOperatorCharacteristic
        (deriv completedNativeOperatorCharacteristic 0) 0 :=
      completedNativeOperatorCharacteristic_differentiableAt_zero.hasDerivAt
    have hFderivAtLine : HasDerivAt completedNativeOperatorCharacteristic
        (deriv completedNativeOperatorCharacteristic 0)
        ((fun u : ℂ => Complex.I * u) 0) := by
      simpa using hFderiv
    have hcomplex : HasDerivAt
        (fun u : ℂ => completedNativeOperatorCharacteristic (Complex.I * u))
        (deriv completedNativeOperatorCharacteristic 0 * Complex.I) 0 :=
      hFderivAtLine.comp (𝕜 := ℂ) (𝕜' := ℂ) 0 hlineComplex
    simpa [line] using hcomplex.comp_ofReal.differentiableAt
  have hjetComplex : DifferentiableAt ℂ
      (deriv completedNativeOperatorCharacteristic) 0 :=
    (completedNativeOperatorCharacteristic_analyticAt
      zero_mem_completedNativeHeightDomain).deriv.differentiableAt
  have hjetLine : DifferentiableAt ℝ
      (fun y : ℝ =>
        deriv completedNativeOperatorCharacteristic (line y)) 0 := by
    have hjetDeriv : HasDerivAt
        (deriv completedNativeOperatorCharacteristic)
        (deriv (deriv completedNativeOperatorCharacteristic) 0) 0 :=
      hjetComplex.hasDerivAt
    have hjetDerivAtLine : HasDerivAt
        (deriv completedNativeOperatorCharacteristic)
        (deriv (deriv completedNativeOperatorCharacteristic) 0)
        ((fun u : ℂ => Complex.I * u) 0) := by
      simpa using hjetDeriv
    have hcomplex : HasDerivAt
        (fun u : ℂ =>
          deriv completedNativeOperatorCharacteristic (Complex.I * u))
        (deriv (deriv completedNativeOperatorCharacteristic) 0 * Complex.I) 0 :=
      hjetDerivAtLine.comp (𝕜 := ℂ) (𝕜' := ℂ) 0 hlineComplex
    simpa [line] using hcomplex.comp_ofReal.differentiableAt
  have hden :
      2 * ‖completedNativeOperatorCharacteristic (line 0)‖ ^ 2 ≠ 0 := by
    have hnorm : ‖completedNativeOperatorCharacteristic (line 0)‖ ≠ 0 := by
      simpa [line] using
        (norm_ne_zero_iff.mpr completedNativeOperatorCharacteristic_zero_ne_zero)
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hnorm)
  have hmodel : DifferentiableAt ℝ model 0 := by
    dsimp only [model]
    exact (differentiableAt_const (c := (1 : ℝ) / 2)).add
      ((hjetLine.norm_sq ℂ).div
        ((differentiableAt_const (c := (2 : ℝ))).mul
          (hFline.norm_sq ℂ)) hden)
  have hpoint : Filter.Tendsto line (nhds 0) (nhds 0) := by
    have hcontinuous : ContinuousAt line 0 := by
      dsimp only [line]
      fun_prop
    simpa [line] using hcontinuous.tendsto
  have hnonzero : ∀ᶠ y : ℝ in nhds 0,
      completedNativeOperatorCharacteristic (line y) ≠ 0 :=
    hpoint.eventually
      (completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
        completedNativeOperatorCharacteristic_zero_ne_zero)
  have heq : completedNativeCentralChiralTotalEnergy =ᶠ[nhds 0] model := by
    filter_upwards [hnonzero] with y hyF
    exact completedNativeNormalizedChiralTraceTotalEnergy_eq hyF
  exact heq.differentiableAt_iff.mpr hmodel

/-- Differentiable spelling of the stationary total-energy law. -/
theorem hasDerivAt_completedNativeCentralChiralTotalEnergy_zero :
    HasDerivAt completedNativeCentralChiralTotalEnergy 0 0 := by
  simpa [deriv_completedNativeCentralChiralTotalEnergy_zero] using
    completedNativeCentralChiralTotalEnergy_differentiableAt_zero.hasDerivAt

/-- The positive diagonal chirality receives the zeroth moment as its exact
first-order energy flow. -/
theorem hasDerivAt_completedNativeCentralPositiveChiralEnergy_zero :
    HasDerivAt completedNativeCentralPositiveChiralEnergy
      (canonicalCompletedNativeLogDerivativeMoment 0) 0 := by
  have h :=
    (hasDerivAt_completedNativeCentralChiralTotalEnergy_zero.add
      hasDerivAt_completedNativeCentralChiralEnergyDifference).const_mul
        ((1 : ℝ) / 2)
  have hfun : completedNativeCentralPositiveChiralEnergy =
      fun y => (1 : ℝ) / 2 *
        (completedNativeCentralChiralTotalEnergy +
          completedNativeCentralChiralEnergyDifference) y := by
    funext y
    simp only [Pi.add_apply]
    rw [completedNativeCentralChiralTotalEnergy_eq_add,
      completedNativeCentralChiralEnergyDifference_eq_sub]
    ring
  rw [hfun]
  have hcoefficient :
      (1 : ℝ) / 2 *
          (0 + 2 * canonicalCompletedNativeLogDerivativeMoment 0) =
        canonicalCompletedNativeLogDerivativeMoment 0 := by
    ring
  rw [hcoefficient] at h
  exact h

/-- The negative chirality loses the same amount, so the first-order total
energy remains stationary without erasing the signed transfer. -/
theorem hasDerivAt_completedNativeCentralNegativeChiralEnergy_zero :
    HasDerivAt completedNativeCentralNegativeChiralEnergy
      (-canonicalCompletedNativeLogDerivativeMoment 0) 0 := by
  have h :=
    (hasDerivAt_completedNativeCentralChiralTotalEnergy_zero.sub
      hasDerivAt_completedNativeCentralChiralEnergyDifference).const_mul
        ((1 : ℝ) / 2)
  have hfun : completedNativeCentralNegativeChiralEnergy =
      fun y => (1 : ℝ) / 2 *
        (completedNativeCentralChiralTotalEnergy -
          completedNativeCentralChiralEnergyDifference) y := by
    funext y
    simp only [Pi.sub_apply]
    rw [completedNativeCentralChiralTotalEnergy_eq_add,
      completedNativeCentralChiralEnergyDifference_eq_sub]
    ring
  rw [hfun]
  have hcoefficient :
      (1 : ℝ) / 2 *
          (0 - 2 * canonicalCompletedNativeLogDerivativeMoment 0) =
        -canonicalCompletedNativeLogDerivativeMoment 0 := by
    ring
  rw [hcoefficient] at h
  exact h

theorem deriv_completedNativeCentralPositiveChiralEnergy_zero :
    deriv completedNativeCentralPositiveChiralEnergy 0 =
      canonicalCompletedNativeLogDerivativeMoment 0 :=
  hasDerivAt_completedNativeCentralPositiveChiralEnergy_zero.deriv

theorem deriv_completedNativeCentralNegativeChiralEnergy_zero :
    deriv completedNativeCentralNegativeChiralEnergy 0 =
      -canonicalCompletedNativeLogDerivativeMoment 0 :=
  hasDerivAt_completedNativeCentralNegativeChiralEnergy_zero.deriv

/-! ## Exact comparison of the two central tilt slopes -/

/-- The signed chiral slope and the positive Green-bulk slope coincide exactly
when the zeroth completed moment equals the independently constructed radial
Green energy.  This theorem exposes the comparison; it does not assume or
prove it. -/
theorem
    deriv_completedNativeCentralChiralEnergyDifference_zero_eq_greenBulk_iff :
    deriv completedNativeCentralChiralEnergyDifference 0 =
        canonicalCentralInfiniteGreenBulkFirstVariation ↔
      canonicalCompletedNativeLogDerivativeMoment 0 =
        Real.log 3 * infiniteReflectedGreenEnergy (1 / 2 : ℂ) := by
  rw [deriv_completedNativeCentralChiralEnergyDifference_zero]
  unfold canonicalCentralInfiniteGreenBulkFirstVariation
  constructor <;> intro h <;> linarith

/-- Difference of the two central slopes, with all factors exposed. -/
theorem
    deriv_completedNativeCentralChiralEnergyDifference_zero_sub_greenBulk :
    deriv completedNativeCentralChiralEnergyDifference 0 -
        canonicalCentralInfiniteGreenBulkFirstVariation =
      2 * (canonicalCompletedNativeLogDerivativeMoment 0 -
        Real.log 3 * infiniteReflectedGreenEnergy (1 / 2 : ℂ)) := by
  rw [deriv_completedNativeCentralChiralEnergyDifference_zero]
  unfold canonicalCentralInfiniteGreenBulkFirstVariation
  ring

/-! ## Separation-regularized ambient defect -/

/-- The ambient-versus-native boundary defect after dividing by the exact
nonzero Hermitian separation on the radial sample grid.  Unlike the raw
defect, this quantity cannot tend to zero merely because the grid collapses
to the center. -/
def canonicalCompletedC3RegularizedAmbientRadialDslopeDefect
    (k N : ℕ) (i j : Fin N) : ℂ :=
  canonicalCompletedC3NormalizedAmbientRadialDslopeDefect k N i j /
    (canonicalCompletedC3AmbientRadialTiltPoint k N j -
      conj (canonicalCompletedC3AmbientRadialTiltPoint k N i))

/-- Exact cancellation of the separation exposes the actual kernel mismatch. -/
theorem canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_eq_kernel_sub
    (k N : ℕ) (i j : Fin N) :
    canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k N i j =
      canonicalCompletedC3NormalizedAmbientResponseKernel
          (canonicalCompletedC3AmbientRadialTiltPoint k N i)
          (canonicalCompletedC3AmbientRadialTiltPoint k N j)
          (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
          (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j) -
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3AmbientRadialTiltPoint k N i)
          (canonicalCompletedC3AmbientRadialTiltPoint k N j) := by
  unfold canonicalCompletedC3RegularizedAmbientRadialDslopeDefect
  rw [canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_eq_mul_kernel_sub]
  exact mul_div_cancel_left₀ _
    (canonicalCompletedC3AmbientRadialTilt_separation_ne_zero k N i j)

private theorem
    deriv_completedNativeGreenNormalizedResponse_zero_eq_moment_zero :
    deriv
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  have h := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0
  simpa [completedNativeGreenResponseTaylorCoefficient,
    iteratedDeriv_one] using h

/-- The regularized radial defect has the honest central limit: normalized
ambient energy minus the zeroth completed-native moment. -/
theorem canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto
    (N : ℕ) (i j : Fin N) :
    Filter.Tendsto
      (fun k : ℕ =>
        canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k N i j)
      Filter.atTop
      (nhds
        (inner ℂ
            (canonicalCompletedC3NormalizedAmbientResponseState 0
              (by norm_num [operatorHeightParameter]))
            (canonicalCompletedC3NormalizedAmbientResponseState 0
              (by norm_num [operatorHeightParameter])) -
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  have hambient :=
    canonicalCompletedC3NormalizedAmbientResponseKernel_ambientRadial_tendsto
      N i j
  have hnative :=
    canonicalCompletedNativePolarizedDslopeKernel_ambientRadial_tendsto N i j
  rw [deriv_completedNativeGreenNormalizedResponse_zero_eq_moment_zero]
    at hnative
  have hsub := hambient.sub hnative
  exact hsub.congr' (Filter.Eventually.of_forall fun k =>
    (canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_eq_kernel_sub
      k N i j).symm)

/-- The complete four-channel correction ledger with the same separation
regularization. -/
def canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger
    (k N : ℕ) (i j : Fin N) : ℂ :=
  canonicalCompletedC3NormalizedAmbientRadialCorrectionLedger k N i j /
    (canonicalCompletedC3AmbientRadialTiltPoint k N j -
      conj (canonicalCompletedC3AmbientRadialTiltPoint k N i))

/-- Once regularized, the correction ledger has the same nontrivial central
limit as the kernel mismatch. -/
theorem canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger_tendsto
    (M N : ℕ) (i j : Fin N) :
    Filter.Tendsto
      (fun k : ℕ =>
        canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger k N i j)
      Filter.atTop
      (nhds
        (inner ℂ
            (canonicalCompletedC3NormalizedAmbientResponseState 0
              (by norm_num [operatorHeightParameter]))
            (canonicalCompletedC3NormalizedAmbientResponseState 0
              (by norm_num [operatorHeightParameter])) -
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  have heq :=
    canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_eventually_eq_ledger
      M N i j
  have hregularized :
      (fun k : ℕ =>
        canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k N i j) =ᶠ[
          Filter.atTop]
        (fun k : ℕ =>
          canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger
            k N i j) := by
    filter_upwards [heq] with k hk
    unfold canonicalCompletedC3RegularizedAmbientRadialDslopeDefect
      canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger
    rw [hk]
  exact
    (canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto
      N i j).congr' hregularized

/-- The regularized complete ledger vanishes precisely when the normalized
ambient center realizes `h₀`.  This is the first honest tilt-orientation
coefficient; raw no-leak before division is strictly weaker. -/
theorem
    canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger_tendsto_zero_iff
    (M N : ℕ) (i j : Fin N) :
    Filter.Tendsto
        (fun k : ℕ =>
          canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger
            k N i j)
        Filter.atTop (nhds 0) ↔
      inner ℂ
          (canonicalCompletedC3NormalizedAmbientResponseState 0
            (by norm_num [operatorHeightParameter]))
          (canonicalCompletedC3NormalizedAmbientResponseState 0
            (by norm_num [operatorHeightParameter])) =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  have hlimit :=
    canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger_tendsto
      M N i j
  constructor
  · intro hzero
    exact sub_eq_zero.mp (tendsto_nhds_unique hlimit hzero)
  · intro hcenter
    have htarget :
        inner ℂ
            (canonicalCompletedC3NormalizedAmbientResponseState 0
              (by norm_num [operatorHeightParameter]))
            (canonicalCompletedC3NormalizedAmbientResponseState 0
              (by norm_num [operatorHeightParameter])) -
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) = 0 :=
      sub_eq_zero.mpr hcenter
    rw [htarget] at hlimit
    exact hlimit

/-- Coordinate-level form of the same first regularized gate.  The positive
ordinary-gradient energy, the exact characteristic weight, and `h₀` are all
visible; no fitted normalization remains. -/
theorem
    canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger_tendsto_zero_iff_gradient
    (M N : ℕ) (i j : Fin N) :
    Filter.Tendsto
        (fun k : ℕ =>
          canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger
            k N i j)
        Filter.atTop (nhds 0) ↔
      ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0)
          (by norm_num [operatorHeightParameter])‖ ^ 2 =
        ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
          canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger_tendsto_zero_iff
    (M := M) (N := N) (i := i) (j := j)]
  rw [inner_self_eq_norm_sq_to_K]
  let hhalf : 0 < (operatorHeightParameter 0).re := by
    norm_num [operatorHeightParameter]
  change
    ((‖canonicalCompletedC3NormalizedAmbientResponseState 0 hhalf‖ : ℂ) ^ 2 =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) ↔ _
  have hcriterion :
      ‖canonicalCompletedC3NormalizedAmbientResponseState 0 hhalf‖ ^ 2 =
          canonicalCompletedNativeLogDerivativeMoment 0 ↔
        ‖canonicalCompletedC3DirichletGradientState
            (operatorHeightParameter 0) hhalf‖ ^ 2 =
          ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
            canonicalCompletedNativeLogDerivativeMoment 0 := by
    simpa only using
      norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero_eq_moment_zero_iff
  constructor
  · intro hcomplex
    have hreal :
        ‖canonicalCompletedC3NormalizedAmbientResponseState 0 hhalf‖ ^ 2 =
          canonicalCompletedNativeLogDerivativeMoment 0 := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_pow] using hcomplex
    exact hcriterion.mp hreal
  · intro hgradient
    have hreal := hcriterion.mpr hgradient
    simpa only [Complex.ofReal_pow] using
      congrArg (fun x : ℝ => (x : ℂ)) hreal

end

end CarrySelfAdjointOperator

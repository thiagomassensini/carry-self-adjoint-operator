import CarrySelfAdjointOperator.CompletedC3ExistingDressedStateAudit
import CarrySelfAdjointOperator.CompletedNativeTfvdEnrichedTaylorMomentIdentification
import CarrySelfAdjointOperator.CompletedNativeRadialHerglotzTwoPoint
import Mathlib.Tactic

/-!
# Low-order audit of the concrete completed C3 dressed state

The concrete one-point state contains three orthogonal channels: ordinary
TFVD, logarithmic TFVD, and the retained precompression residual.  The raw
TFVD Taylor carrier used by the older moment-identification gate contains
only the first two.

This file opens the zeroth Gram coefficient before any scalar moment
identification.  The result is an exact strict decomposition: the dressed
central Gram is the old enriched zeroth Gram plus a nonzero positive residual
energy.  Consequently the two candidate identifications with `h₀` cannot
both hold.  This is a carrier-level obstruction, independent of theta and of
the unproved real-axis sewing statement.
-/

open scoped ComplexOrder InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## The retained residual is genuinely present at the center -/

/-- The fixed generator of the completed residual ray is nonzero. -/
theorem completedTfvdResidualGenerator_ne_zero :
    completedTfvdResidualGenerator ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg (fun state => state.2 1) hzero
  simp [completedTfvdResidualGenerator, lp.single_apply] at hcoordinate

/-- The fixed residual-ray generator has unit norm in its Hilbert
presentation. -/
@[simp] theorem norm_completedTfvdResidualGenerator_toLp :
    ‖(WithLp.toLp 2 completedTfvdResidualGenerator :
      CanonicalCompletedC3RealAxisResidualHilbert)‖ = 1 := by
  simp [completedTfvdResidualGenerator]

/-- The reflected Green coefficient at the centered height is strictly
positive. -/
theorem infiniteReflectedGreenEnergy_half_pos :
    0 < infiniteReflectedGreenEnergy (1 / 2 : ℂ) := by
  exact infiniteReflectedGreenEnergy_pos (by
    constructor <;> norm_num [genuineCriticalStrip])

/-- Hence the retained residual coordinate of the concrete dressed state is
not zero at the center. -/
theorem canonicalCompletedC3RealAxisResidualState_zero_ne_zero :
    canonicalCompletedC3RealAxisResidualState 0 ≠ 0 := by
  intro hzero
  have hzero' := congrArg WithLp.ofLp hzero
  simp only [canonicalCompletedC3RealAxisResidualState,
    WithLp.ofLp_toLp, WithLp.ofLp_zero, Complex.zero_re,
    Complex.ofReal_zero] at hzero'
  have henergy : infiniteReflectedGreenEnergy
      (operatorHeightParameter (0 : ℂ)) ≠ 0 := by
    rw [show operatorHeightParameter (0 : ℂ) = (1 / 2 : ℂ) by
      simp [operatorHeightParameter]]
    exact ne_of_gt infiniteReflectedGreenEnergy_half_pos
  exact (smul_ne_zero henergy completedTfvdResidualGenerator_ne_zero) hzero'

/-! ## Exact central Gram split -/

/-- At the center, the ordinary and logarithmic coordinates of the concrete
dressed state are exactly the two coordinates of the old enriched zeroth
Taylor jet. -/
theorem canonicalCompletedC3RealAxisPositiveKernel_zero_zero_eq_enriched_add_residual :
    canonicalCompletedC3RealAxisPositiveKernel 0 0 =
      inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0) +
        ((inner ℝ
          (canonicalCompletedC3RealAxisResidualState 0)
          (canonicalCompletedC3RealAxisResidualState 0) : ℝ) : ℂ) := by
  rw [canonicalCompletedC3RealAxisPositiveKernel_eq_sourceChannelSum,
    inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero]
  simp [canonicalCompletedC3RealAxisOrdinaryState,
    canonicalCompletedC3RealAxisLogJetState,
    canonicalCompletedC3HilbertState, operatorHeightParameter]

/-- Real-part form of the same decomposition. -/
theorem canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_eq_enriched_add_residual :
    (canonicalCompletedC3RealAxisPositiveKernel 0 0).re =
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re +
        ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  rw [canonicalCompletedC3RealAxisPositiveKernel_zero_zero_eq_enriched_add_residual]
  simp only [Complex.add_re, Complex.ofReal_re,
    real_inner_self_eq_norm_sq]

/-- The extra central residual energy is strictly positive. -/
theorem canonicalCompletedC3RealAxisResidualState_zero_norm_sq_pos :
    0 < ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  exact sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr canonicalCompletedC3RealAxisResidualState_zero_ne_zero)

/-- The central residual Gram contribution is the square of the reflected
Green energy coefficient; this quadratic normalization is important when it
is compared with two-point ledgers in which the same residual can occur in
linear or crossed channels. -/
theorem canonicalCompletedC3RealAxisResidualState_zero_norm_sq_eq_energy_sq :
    ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) ^ 2 := by
  unfold canonicalCompletedC3RealAxisResidualState
  simp only [Complex.zero_re, Complex.ofReal_zero]
  rw [show operatorHeightParameter (0 : ℂ) = (1 / 2 : ℂ) by
    simp [operatorHeightParameter]]
  rw [show WithLp.toLp 2
      (infiniteReflectedGreenEnergy (1 / 2 : ℂ) •
        completedTfvdResidualGenerator) =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) •
        (WithLp.toLp 2 completedTfvdResidualGenerator :
          CanonicalCompletedC3RealAxisResidualHilbert) by rfl]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos infiniteReflectedGreenEnergy_half_pos,
    norm_completedTfvdResidualGenerator_toLp, mul_one]

/-- Therefore the concrete dressed central Gram is strictly larger than the
ordinary-plus-logarithmic enriched central Gram. -/
theorem canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_gt_enriched :
    (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re <
      (canonicalCompletedC3RealAxisPositiveKernel 0 0).re := by
  rw [canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_eq_enriched_add_residual]
  exact lt_add_of_pos_right _
    canonicalCompletedC3RealAxisResidualState_zero_norm_sq_pos

/-! ## The residual channel at first odd order -/

/-- Reversing native time reflects the rotating real-plane sample across its
first coordinate. -/
theorem finiteNativeCarry_nativeState_neg_time (time : ℝ) (n : ℕ) :
    FiniteNativeCarryOperator.Operator.nativeState (-time) n =
      ((FiniteNativeCarryOperator.Operator.nativeState time n).1,
        -(FiniteNativeCarryOperator.Operator.nativeState time n).2) := by
  apply Prod.ext <;>
    simp [FiniteNativeCarryOperator.Operator.nativeState,
      Real.cos_neg, Real.sin_neg]

/-- Complex packaging turns the same time reversal into conjugation. -/
theorem packagedNativeSlope_neg_time (time : ℝ) (n : ℕ) :
    nativeCarryRealPlaneComplexPackaging
        (FiniteNativeCarryOperator.Operator.nativeState (-time) (n + 2) -
          FiniteNativeCarryOperator.Operator.nativeState (-time) (n + 1)) =
      starRingEnd ℂ
        (nativeCarryRealPlaneComplexPackaging
          (FiniteNativeCarryOperator.Operator.nativeState time (n + 2) -
            FiniteNativeCarryOperator.Operator.nativeState time (n + 1))) := by
  rw [finiteNativeCarry_nativeState_neg_time,
    finiteNativeCarry_nativeState_neg_time]
  apply Complex.ext
  · simp [nativeCarryRealPlaneComplexPackaging]
  · simp [nativeCarryRealPlaneComplexPackaging]
    ring

/-- Every finite native slope energy is even in time. -/
theorem finitePackagedNativeSlopeEnergy_neg_time (M : ℕ) (time : ℝ) :
    finitePackagedNativeSlopeEnergy M (-time) =
      finitePackagedNativeSlopeEnergy M time := by
  unfold finitePackagedNativeSlopeEnergy
  apply Finset.sum_congr rfl
  intro n hn
  rw [packagedNativeSlope_neg_time]
  simp [mul_comm]

/-- The completed reflected Green energy is even on the native line. -/
theorem infiniteReflectedGreenEnergy_nativeLine_neg (time : ℝ) :
    infiniteReflectedGreenEnergy (nativeLine (-time)) =
      infiniteReflectedGreenEnergy (nativeLine time) := by
  have hneg := finiteReflectedGradientPairing_re_tendsto_infiniteEnergy
    (nativeLine_mem_genuineCriticalStrip (-time))
  have hpos := finiteReflectedGradientPairing_re_tendsto_infiniteEnergy
    (nativeLine_mem_genuineCriticalStrip time)
  apply tendsto_nhds_unique hneg
  apply hpos.congr'
  filter_upwards with M
  rw [finiteReflectedGradientPairing_nativeLine_eq_nativeSlopeEnergy,
    finiteReflectedGradientPairing_nativeLine_eq_nativeSlopeEnergy,
    finitePackagedNativeSlopeEnergy_neg_time]

/-- Therefore the scalar coefficient of the retained residual ray is even
on the real sampling axis. -/
theorem canonicalCompletedC3ResidualCoefficient_neg (time : ℝ) :
    infiniteReflectedGreenEnergy
        (operatorHeightParameter ((-time : ℝ) : ℂ)) =
      infiniteReflectedGreenEnergy
        (operatorHeightParameter (time : ℂ)) := by
  rw [operatorHeightParameter_ofReal_eq_nativeLine,
    operatorHeightParameter_ofReal_eq_nativeLine]
  exact infiniteReflectedGreenEnergy_nativeLine_neg time

/-- One scalar summand of the reflected Green energy on the native line. -/
def canonicalCompletedC3ResidualEnergyMode (n : ℕ) (time : ℝ) : ℝ :=
  (starRingEnd ℂ (positiveDirichletGradient (nativeLine time) n) *
    positiveDirichletGradient (nativeLine time) n).re

/-- Parameter derivative of one residual-energy summand. -/
def canonicalCompletedC3ResidualEnergyModeFirst (n : ℕ) (time : ℝ) : ℝ :=
  let slope := positiveDirichletGradient (nativeLine time) n
  let slopeFirst :=
    -Complex.I * positiveLogDirichletGradient (nativeLine time) n
  (starRingEnd ℂ slopeFirst * slope +
    starRingEnd ℂ slope * slopeFirst).re

/-- Differentiating one native slope with respect to real time inserts the
logarithmic slope and the universal phase `-I`. -/
theorem hasDerivAt_positiveDirichletGradient_nativeLine
    (n : ℕ) (time : ℝ) :
    HasDerivAt
      (fun y : ℝ => positiveDirichletGradient (nativeLine y) n)
      (-Complex.I * positiveLogDirichletGradient (nativeLine time) n)
      time := by
  have hleft := hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm
    (n + 2) (by omega) (nativeLine time)
  have hright := hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm
    (n + 1) (by omega) (nativeLine time)
  have hslope : HasDerivAt
      (fun s : ℂ => positiveDirichletGradient s n)
      (-positiveLogDirichletGradient (nativeLine time) n)
      (nativeLine time) := by
    refine ((hleft.sub hright).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun s => by
        simp [positiveDirichletGradient])
    · simp [positiveLogDirichletGradient,
        positiveLogDirichletValue_eq_natLogDirichletTerm]
      ring
  let complexLine : ℂ → ℂ := fun z => (1 / 2 : ℂ) + z * Complex.I
  have hline : HasDerivAt complexLine Complex.I (time : ℂ) := by
    refine ((((hasDerivAt_const (x := (time : ℂ)) (c := (1 / 2 : ℂ))).add
      ((hasDerivAt_id (time : ℂ)).mul_const Complex.I)).congr_of_eventuallyEq ?_).congr_deriv ?_)
    · exact Filter.Eventually.of_forall (fun z => rfl)
    · ring
  have hcomplex := hslope.comp (time : ℂ) hline
  have hreal := hcomplex.comp_ofReal
  convert hreal using 1
  · funext y
    simp [complexLine, nativeLine]
  · ring

/-- Each scalar residual-energy mode has the expected product derivative. -/
theorem hasDerivAt_canonicalCompletedC3ResidualEnergyMode
    (n : ℕ) (time : ℝ) :
    HasDerivAt (canonicalCompletedC3ResidualEnergyMode n)
      (canonicalCompletedC3ResidualEnergyModeFirst n time) time := by
  have hslope := hasDerivAt_positiveDirichletGradient_nativeLine n time
  have hconj := hasDerivAt_complexConj hslope
  have hproduct := hconj.mul hslope
  have hre :=
    (Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp time hproduct.hasFDerivAt
  refine (hre.hasDerivAt.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun y => by
      simp [canonicalCompletedC3ResidualEnergyMode,
        Complex.reCLM_apply])
  · simp [canonicalCompletedC3ResidualEnergyModeFirst,
      Complex.reCLM_apply]

/-- Each individual energy mode is even. -/
theorem canonicalCompletedC3ResidualEnergyMode_neg
    (n : ℕ) (time : ℝ) :
    canonicalCompletedC3ResidualEnergyMode n (-time) =
      canonicalCompletedC3ResidualEnergyMode n time := by
  unfold canonicalCompletedC3ResidualEnergyMode
  rw [positiveDirichletGradient_nativeLine_eq_packagedNativeSlope,
    positiveDirichletGradient_nativeLine_eq_packagedNativeSlope,
    packagedNativeSlope_neg_time]
  simp [mul_comm]

/-- The derivative of every individual even mode vanishes at the center. -/
@[simp] theorem canonicalCompletedC3ResidualEnergyModeFirst_zero
    (n : ℕ) :
    canonicalCompletedC3ResidualEnergyModeFirst n 0 = 0 := by
  have hforward :=
    hasDerivAt_canonicalCompletedC3ResidualEnergyMode n 0
  have hbackward : HasDerivAt
      (fun time : ℝ => canonicalCompletedC3ResidualEnergyMode n (-time))
      (-canonicalCompletedC3ResidualEnergyModeFirst n 0) 0 := by
    have houter : HasDerivAt (canonicalCompletedC3ResidualEnergyMode n)
        (canonicalCompletedC3ResidualEnergyModeFirst n 0) (-0) := by
      simpa using hforward
    refine ((houter.comp 0 (hasDerivAt_neg' (0 : ℝ))).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ => rfl)
    · ring
  have heven :
      (fun time : ℝ => canonicalCompletedC3ResidualEnergyMode n (-time)) =
        canonicalCompletedC3ResidualEnergyMode n := by
    funext time
    exact canonicalCompletedC3ResidualEnergyMode_neg n time
  rw [heven] at hbackward
  have hunique := hforward.unique hbackward
  linarith

/-- The infinite reflected energy on the native line is literally the sum of
the scalar energy modes. -/
theorem infiniteReflectedGreenEnergy_nativeLine_eq_tsum_modes (time : ℝ) :
    infiniteReflectedGreenEnergy (nativeLine time) =
      ∑' n : ℕ, canonicalCompletedC3ResidualEnergyMode n time := by
  rw [infiniteReflectedGreenEnergy, infiniteReflectedGradientPairing,
    Complex.re_tsum
      (summable_finiteReflectedGradientEdge
        (nativeLine_mem_genuineCriticalStrip time))]
  congr 1
  funext n
  rw [finiteReflectedGradientEdge,
    nativeLine_eq_criticalLineParameter,
    reflectedParameter_criticalLineParameter]
  unfold canonicalCompletedC3ResidualEnergyMode
  rw [nativeLine_eq_criticalLineParameter]

/-- On the local interval used for termwise differentiation, the native-line
parameter has a uniform norm bound. -/
theorem norm_nativeLine_le_two {time : ℝ}
    (htime : time ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖nativeLine time‖ ≤ 2 := by
  rw [show nativeLine time = (1 / 2 : ℂ) + (time : ℂ) * Complex.I by
    rfl]
  calc
    ‖(1 / 2 : ℂ) + (time : ℂ) * Complex.I‖ ≤
        ‖(1 / 2 : ℂ)‖ + ‖(time : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) + |time| := by simp
    _ ≤ 2 := by
      have habs : |time| < 1 := abs_lt.mpr htime
      linarith

/-- Summable local majorant for the first derivatives of the residual-energy
modes. -/
def canonicalCompletedC3ResidualEnergyFirstMajorant (n : ℕ) : ℝ :=
  36 * ((n + 1 : ℕ) : ℝ) ^ (-11 / 4 : ℝ)

theorem summable_canonicalCompletedC3ResidualEnergyFirstMajorant :
    Summable canonicalCompletedC3ResidualEnergyFirstMajorant := by
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ (-11 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := hbase.comp_injective
    (show Function.Injective (fun n : ℕ => n + 1) by
      intro a b hab
      exact Nat.add_right_cancel hab)
  change Summable (fun n : ℕ =>
    36 * ((n + 1 : ℕ) : ℝ) ^ (-11 / 4 : ℝ))
  exact hshift.mul_left 36

/-- Uniform derivative bound on `(-1,1)`.  The ordinary slope contributes
power `-3/2`, the logarithmic slope power `-5/4`, hence the summable product
power `-11/4`. -/
theorem norm_canonicalCompletedC3ResidualEnergyModeFirst_le
    (n : ℕ) {time : ℝ} (htime : time ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖canonicalCompletedC3ResidualEnergyModeFirst n time‖ ≤
      canonicalCompletedC3ResidualEnergyFirstMajorant n := by
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hslopeRaw := norm_positiveDirichletGradient_le
    (s := nativeLine time) (by simp [nativeLine]) n
  have hslope :
      ‖positiveDirichletGradient (nativeLine time) n‖ ≤
        2 * x ^ (-3 / 2 : ℝ) := by
    calc
      _ ≤ ‖nativeLine time‖ *
          x ^ (-(nativeLine time).re - 1) := hslopeRaw
      _ = ‖nativeLine time‖ * x ^ (-3 / 2 : ℝ) := by
        congr 2
        simp [nativeLine]
        ring
      _ ≤ 2 * x ^ (-3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (norm_nativeLine_le_two htime)
          (Real.rpow_nonneg hx.le _)
  have hlogRaw := norm_positiveLogDirichletGradient_le
    (s := nativeLine time) (by simp [nativeLine]) n
  have hcoefficient :
      ‖nativeLine time‖ / ((nativeLine time).re / 2) + 1 ≤ 9 := by
    have hnorm := norm_nativeLine_le_two htime
    rw [show (nativeLine time).re = (1 / 2 : ℝ) by
      simp [nativeLine]]
    norm_num
    linarith
  have hlog :
      ‖positiveLogDirichletGradient (nativeLine time) n‖ ≤
        9 * x ^ (-5 / 4 : ℝ) := by
    calc
      _ ≤ (‖nativeLine time‖ / ((nativeLine time).re / 2) + 1) *
          x ^ (-(nativeLine time).re / 2 - 1) := hlogRaw
      _ = (‖nativeLine time‖ / ((nativeLine time).re / 2) + 1) *
          x ^ (-5 / 4 : ℝ) := by
        congr 2
        simp [nativeLine]
        ring
      _ ≤ 9 * x ^ (-5 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hcoefficient
          (Real.rpow_nonneg hx.le _)
  let slope := positiveDirichletGradient (nativeLine time) n
  let slopeFirst :=
    -Complex.I * positiveLogDirichletGradient (nativeLine time) n
  have hslopeFirst : ‖slopeFirst‖ ≤ 9 * x ^ (-5 / 4 : ℝ) := by
    simpa [slopeFirst] using hlog
  have hproduct :
      2 * (‖slopeFirst‖ * ‖slope‖) ≤
        36 * x ^ (-11 / 4 : ℝ) := by
    have hmul := mul_le_mul hslopeFirst hslope
      (norm_nonneg _) (mul_nonneg (by norm_num)
        (Real.rpow_nonneg hx.le _))
    calc
      2 * (‖slopeFirst‖ * ‖slope‖) ≤
          2 * ((9 * x ^ (-5 / 4 : ℝ)) *
            (2 * x ^ (-3 / 2 : ℝ))) := by nlinarith
      _ = 36 * (x ^ (-5 / 4 : ℝ) * x ^ (-3 / 2 : ℝ)) := by ring
      _ = 36 * x ^ (-11 / 4 : ℝ) := by
        rw [← Real.rpow_add hx]
        congr 2
        ring
  unfold canonicalCompletedC3ResidualEnergyModeFirst
    canonicalCompletedC3ResidualEnergyFirstMajorant
  dsimp only
  rw [Real.norm_eq_abs]
  calc
    |(starRingEnd ℂ slopeFirst * slope +
        starRingEnd ℂ slope * slopeFirst).re| ≤
        ‖starRingEnd ℂ slopeFirst * slope +
          starRingEnd ℂ slope * slopeFirst‖ := Complex.abs_re_le_norm _
    _ ≤ ‖starRingEnd ℂ slopeFirst * slope‖ +
        ‖starRingEnd ℂ slope * slopeFirst‖ := norm_add_le _ _
    _ = 2 * (‖slopeFirst‖ * ‖slope‖) := by
      simp [mul_comm]
      ring
    _ ≤ 36 * x ^ (-11 / 4 : ℝ) := hproduct
    _ = 36 * ((n + 1 : ℕ) : ℝ) ^ (-11 / 4 : ℝ) := by rfl

/-- The scalar modes are summable at the center. -/
theorem summable_canonicalCompletedC3ResidualEnergyMode_zero :
    Summable (fun n : ℕ =>
      canonicalCompletedC3ResidualEnergyMode n 0) := by
  have hmajorant := summable_norm_finiteReflectedGradientEdge
    (nativeLine_mem_genuineCriticalStrip 0)
  apply hmajorant.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs]
  calc
    |canonicalCompletedC3ResidualEnergyMode n 0| ≤
        ‖finiteReflectedGradientEdge n (nativeLine 0)‖ := by
      rw [finiteReflectedGradientEdge,
        nativeLine_eq_criticalLineParameter,
        reflectedParameter_criticalLineParameter]
      unfold canonicalCompletedC3ResidualEnergyMode
      rw [nativeLine_eq_criticalLineParameter]
      exact Complex.abs_re_le_norm _

/-- The retained residual coefficient is differentiable at the center and
its first odd derivative is exactly zero.  This is the analytic fact needed
to decide whether the residual contaminates the `(1,1)` gate. -/
theorem hasDerivAt_canonicalCompletedC3ResidualCoefficient_zero :
    HasDerivAt
      (fun time : ℝ => infiniteReflectedGreenEnergy
        (operatorHeightParameter (time : ℂ))) 0 0 := by
  have hsum : HasDerivAt
      (fun time : ℝ =>
        ∑' n : ℕ, canonicalCompletedC3ResidualEnergyMode n time)
      (∑' n : ℕ, canonicalCompletedC3ResidualEnergyModeFirst n 0) 0 :=
    hasDerivAt_tsum_of_isPreconnected
      (g := canonicalCompletedC3ResidualEnergyMode)
      (g' := canonicalCompletedC3ResidualEnergyModeFirst)
      (u := canonicalCompletedC3ResidualEnergyFirstMajorant)
      (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
      summable_canonicalCompletedC3ResidualEnergyFirstMajorant
      isOpen_Ioo isPreconnected_Ioo
      (fun n time _ =>
        hasDerivAt_canonicalCompletedC3ResidualEnergyMode n time)
      (fun n _ htime =>
        norm_canonicalCompletedC3ResidualEnergyModeFirst_le n htime)
      (by norm_num) summable_canonicalCompletedC3ResidualEnergyMode_zero
      (by norm_num)
  have hsumZero :
      (∑' n : ℕ, canonicalCompletedC3ResidualEnergyModeFirst n 0) = 0 := by
    simp
  rw [hsumZero] at hsum
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv rfl
  exact Filter.Eventually.of_forall (fun time => by
    change infiniteReflectedGreenEnergy
        (operatorHeightParameter (time : ℂ)) =
      ∑' n : ℕ, canonicalCompletedC3ResidualEnergyMode n time
    rw [operatorHeightParameter_ofReal_eq_nativeLine,
      infiniteReflectedGreenEnergy_nativeLine_eq_tsum_modes])

/-- Unconditional form of the first-odd flatness obtained by combining
termwise differentiability with the exact time-reversal symmetry. -/
theorem canonicalCompletedC3ResidualCoefficient_deriv_zero :
    deriv
      (fun time : ℝ => infiniteReflectedGreenEnergy
        (operatorHeightParameter (time : ℂ))) 0 = 0 :=
  hasDerivAt_canonicalCompletedC3ResidualCoefficient_zero.deriv

/-- Canonical coefficient-level first jet of the retained residual ray. -/
def canonicalCompletedC3ResidualFirstJet :
    NativeGpreTfvdCompletedPrecompressionSource :=
  deriv
      (fun time : ℝ => infiniteReflectedGreenEnergy
        (operatorHeightParameter (time : ℂ))) 0 •
    completedTfvdResidualGenerator

/-- The retained residual is present at order zero but contributes no first
odd jet. -/
@[simp] theorem canonicalCompletedC3ResidualFirstJet_eq_zero :
    canonicalCompletedC3ResidualFirstJet = 0 := by
  rw [canonicalCompletedC3ResidualFirstJet,
    canonicalCompletedC3ResidualCoefficient_deriv_zero]
  simp

/-- Abstract symmetry lemma used by the unconditional differentiability
calculation above: any center derivative of the even residual coefficient
must vanish. -/
theorem canonicalCompletedC3ResidualCoefficient_firstDerivative_eq_zero
    {derivative : ℝ}
    (hderiv : HasDerivAt
      (fun time : ℝ => infiniteReflectedGreenEnergy
        (operatorHeightParameter (time : ℂ))) derivative 0) :
    derivative = 0 := by
  let coefficient := fun time : ℝ => infiniteReflectedGreenEnergy
    (operatorHeightParameter (time : ℂ))
  have hderiv' : HasDerivAt coefficient derivative (-0) := by
    simpa [coefficient] using hderiv
  have hneg : HasDerivAt (fun time : ℝ => coefficient (-time))
      (-derivative) 0 := by
    refine ((hderiv'.comp 0 (hasDerivAt_neg' (0 : ℝ))).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ => rfl)
    · ring
  have heven : (fun time : ℝ => coefficient (-time)) = coefficient := by
    funext time
    exact canonicalCompletedC3ResidualCoefficient_neg time
  rw [heven] at hneg
  have hunique := hderiv.unique hneg
  linarith

/-! ## The first odd dressed coefficient jet -/

/-- Canonical isometric inclusion of the ordinary/logarithmic Taylor carrier
into the concrete positive carrier, with zero residual coordinate. -/
def canonicalCompletedC3EnrichedTaylorToPositiveCarrier
    (state : CanonicalCompletedNativeTfvdEnrichedTaylorCarrier) :
    CanonicalCompletedC3RealAxisPositiveCarrier :=
  WithLp.toLp 2
    (canonicalCompletedGreenFrameParsevalAnalysis state.fst,
      WithLp.toLp 2
        (canonicalCompletedGreenFrameParsevalAnalysis state.snd, 0))

/-- The inclusion is exactly isometric at the Gram level. -/
theorem canonicalCompletedC3EnrichedTaylorToPositiveCarrier_inner
    (state₁ state₂ : CanonicalCompletedNativeTfvdEnrichedTaylorCarrier) :
    inner ℂ (canonicalCompletedC3EnrichedTaylorToPositiveCarrier state₁)
        (canonicalCompletedC3EnrichedTaylorToPositiveCarrier state₂) =
      inner ℂ state₁ state₂ := by
  unfold canonicalCompletedC3EnrichedTaylorToPositiveCarrier
  change
    inner ℂ (canonicalCompletedGreenFrameParsevalAnalysis state₁.fst)
          (canonicalCompletedGreenFrameParsevalAnalysis state₂.fst) +
        (inner ℂ (canonicalCompletedGreenFrameParsevalAnalysis state₁.snd)
            (canonicalCompletedGreenFrameParsevalAnalysis state₂.snd) +
          inner ℂ (0 : RealHilbertComplexification
            CanonicalCompletedC3RealAxisResidualHilbert) 0) =
      inner ℂ state₁ state₂
  rw [canonicalCompletedGreenFrameParsevalAnalysis_inner,
    canonicalCompletedGreenFrameParsevalAnalysis_inner,
    WithLp.prod_inner_apply]
  simp

/-- Coefficient-level first odd jet of the dressed carrier.  The residual
coordinate is zero by the proved first-order flatness, so this is the old
enriched TFVD jet transported isometrically into the concrete carrier. -/
def canonicalCompletedC3DressedFirstOddCoefficientJet :
    CanonicalCompletedC3RealAxisPositiveCarrier :=
  canonicalCompletedC3EnrichedTaylorToPositiveCarrier
    (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)

/-- The dressed first-odd coefficient Gram is exactly the existing enriched
TFVD `(1,1)` Gram; no residual correction survives. -/
theorem inner_canonicalCompletedC3DressedFirstOddCoefficientJet :
    inner ℂ canonicalCompletedC3DressedFirstOddCoefficientJet
        canonicalCompletedC3DressedFirstOddCoefficientJet =
      inner ℂ (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1) := by
  exact canonicalCompletedC3EnrichedTaylorToPositiveCarrier_inner _ _

/-- The dressed first odd coefficient jet is already nonzero, independently
of its still-open scalar identification with `h₁`. -/
theorem canonicalCompletedC3DressedFirstOddCoefficientJet_ne_zero :
    canonicalCompletedC3DressedFirstOddCoefficientJet ≠ 0 := by
  intro hzero
  have hinner := congrArg Complex.re
    inner_canonicalCompletedC3DressedFirstOddCoefficientJet
  rw [hzero, inner_zero_left, Complex.zero_re] at hinner
  have hpos := canonicalCompletedNativeTfvdFirstOddDiagonal_pos
  linarith

/-- After residual flatness is proved, identification of the dressed first
odd coefficient Gram with `h₁` is literally the already named raw TFVD gate.
No new normalization condition appears at odd order one. -/
theorem canonicalCompletedC3DressedFirstOddMomentIdentification_iff :
    (inner ℂ canonicalCompletedC3DressedFirstOddCoefficientJet
        canonicalCompletedC3DressedFirstOddCoefficientJet).re =
        canonicalCompletedNativeLogDerivativeMoment 1 ↔
      CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification := by
  rw [inner_canonicalCompletedC3DressedFirstOddCoefficientJet]
  rfl

/-! ## Consequence for the proposed `h₀` identification -/

/-- Exact remaining central scalar defect of the concrete dressed state. -/
def canonicalCompletedC3ConcreteDressedCentralMomentDefect : ℝ :=
  (canonicalCompletedC3RealAxisPositiveKernel 0 0).re -
    canonicalCompletedNativeLogDerivativeMoment 0

/-- The central defect is the old ordinary/logarithmic defect plus the
strictly positive retained residual energy. -/
theorem canonicalCompletedC3ConcreteDressedCentralMomentDefect_eq :
    canonicalCompletedC3ConcreteDressedCentralMomentDefect =
      ((inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
        canonicalCompletedNativeLogDerivativeMoment 0) +
      ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  rw [canonicalCompletedC3ConcreteDressedCentralMomentDefect,
    canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_eq_enriched_add_residual]
  ring

/-- Thus closing the concrete dressed central moment is exactly a negative
residual correction to the old enriched central defect. -/
theorem canonicalCompletedC3ConcreteDressedCentralMomentDefect_eq_zero_iff :
    canonicalCompletedC3ConcreteDressedCentralMomentDefect = 0 ↔
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
        canonicalCompletedNativeLogDerivativeMoment 0 =
          -‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  rw [canonicalCompletedC3ConcreteDressedCentralMomentDefect_eq]
  constructor <;> intro h <;> linarith

/-- The old enriched zeroth identification and the concrete dressed zeroth
identification with the same scalar moment are mutually incompatible.  This
does not choose either identification; it pinpoints the first vector-level
failure as the retained nonzero residual coordinate. -/
theorem not_enriched_zero_and_concrete_dressed_zero_moment_identifications :
    ¬ ((inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re =
          canonicalCompletedNativeLogDerivativeMoment 0 ∧
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re =
          canonicalCompletedNativeLogDerivativeMoment 0) := by
  rintro ⟨henriched, hdressed⟩
  have hstrict :=
    canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_gt_enriched
  rw [henriched, hdressed] at hstrict
  exact (lt_irrefl _ hstrict)

end

end CarrySelfAdjointOperator

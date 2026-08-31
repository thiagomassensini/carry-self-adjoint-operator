import CarrySelfAdjointOperator.CompletedNativeExpandedStructuralBlockProbe
import CarrySelfAdjointOperator.CompletedNativeDslopeSamplePositivity
import CarrySelfAdjointOperator.CompletedC3RecoveredDslopePositivityGate
import CarrySelfAdjointOperator.CompletedNativeHermiteBiehlerChiralTrace
import Mathlib.Tactic

/-!
# All-order chiral Hankel dominance

The expanded completed C3 carrier is an honest eight-channel Hilbert Gram
block, but the completed-native logarithmic moments are read from it through
the chiral signature and one additional derivative forced by the spectral
separation.  This module records the resulting all-order matrices before any
operator construction.

The even and odd regularized signature matrices below are proved to be
exactly the canonical Hankel and shifted-Hankel towers.  Consequently their
strict Loewner positivity is neither weaker nor stronger than
`CanonicalCompletedNativeStieltjesPositivity`: it is its concrete chiral
spelling.  In particular, positivity of the unregularized eight-channel Gram
block alone does not discharge this gate.

No positivity, zero-set, spectral, or confinement hypothesis is introduced.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-! ## Exact centered scalar audit -/

/-- At the centered left endpoint, the two normalized scalar chiral kernels
have constant sum.  The logarithmic response therefore lives entirely in
their signed first and higher variations, not in their positive total energy.
-/
theorem completedNativeNormalizedChiralTraceKernel_center_sum
    {z : ℂ} (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeNormalizedPositiveChiralTraceKernel 0 z +
      completedNativeNormalizedNegativeChiralTraceKernel 0 z = (2 : ℂ)⁻¹ := by
  unfold completedNativeNormalizedPositiveChiralTraceKernel
    completedNativeNormalizedNegativeChiralTraceKernel
    completedNativeNormalizedPositiveChiralTraceState
    completedNativeNormalizedNegativeChiralTraceState
  simp only [inner_smul_left, inner_smul_right]
  rw [inner_completedScalarBoundaryPositivePolarization,
    inner_completedScalarBoundaryNegativePolarization,
    completedNativeFNegFPrime_positiveCombination,
    completedNativeFNegFPrime_positiveCombination,
    completedNativeFNegFPrime_negativeCombination,
    completedNativeFNegFPrime_negativeCombination,
    completedNativePositiveHermiteBiehlerCoordinate_zero,
    completedNativeNegativeHermiteBiehlerCoordinate_zero]
  simp only [RCLike.inner_apply]
  have hstar0 :=
    completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel 0
  simp only [map_zero, neg_zero] at hstar0
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  have hF0 : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  unfold canonicalCompletedC3FullWronskianChiralNormalization
    completedNativePositiveHermiteBiehlerCoordinate
    completedNativeNegativeHermiteBiehlerCoordinate
  simp only [map_inv₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_neg]
  rw [← hstar0]
  have hsqrtSq : ((((Real.sqrt 2 : ℝ) : ℂ)) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  field_simp [hsqrt, hF0, hzF]
  rw [hsqrtSq]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Quarter-turned positive center-pinned scalar channel. -/
def completedNativeCenteredPositiveChiralResponse (z : ℂ) : ℂ :=
  Complex.I * completedNativeNormalizedPositiveChiralTraceKernel 0 z

/-- Quarter-turned negative center-pinned scalar channel. -/
def completedNativeCenteredNegativeChiralResponse (z : ℂ) : ℂ :=
  Complex.I * completedNativeNormalizedNegativeChiralTraceKernel 0 z

/-- The positive channel is a constant quarter-energy plus one half of the
completed logarithmic response. -/
theorem completedNativeCenteredPositiveChiralResponse_eq
    {z : ℂ} (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeCenteredPositiveChiralResponse z =
      Complex.I / 4 +
        completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z / 2 := by
  have hsum := completedNativeNormalizedChiralTraceKernel_center_sum hzF
  have hdiff := completedNativeScalarChiralBalanceResponse_eq_completed hzF
  unfold completedNativeScalarChiralBalanceResponse at hdiff
  unfold completedNativeCenteredPositiveChiralResponse
  linear_combination (Complex.I / 2) * hsum + (1 / 2 : ℂ) * hdiff

/-- The negative channel carries the opposite half-variation around the same
constant quarter-energy. -/
theorem completedNativeCenteredNegativeChiralResponse_eq
    {z : ℂ} (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeCenteredNegativeChiralResponse z =
      Complex.I / 4 -
        completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z / 2 := by
  have hsum := completedNativeNormalizedChiralTraceKernel_center_sum hzF
  have hdiff := completedNativeScalarChiralBalanceResponse_eq_completed hzF
  unfold completedNativeScalarChiralBalanceResponse at hdiff
  unfold completedNativeCenteredNegativeChiralResponse
  linear_combination (Complex.I / 2) * hsum - (1 / 2 : ℂ) * hdiff

/-- The positive chiral response and its explicit half-response formula agree
as analytic germs at the center. -/
theorem completedNativeCenteredPositiveChiralResponse_eventuallyEq :
    completedNativeCenteredPositiveChiralResponse =ᶠ[nhds 0]
      (fun z => Complex.I / 4 +
        completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z / 2) := by
  have hnonzero : ∀ᶠ z in nhds (0 : ℂ),
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hnonzero] with z hzF
  exact completedNativeCenteredPositiveChiralResponse_eq hzF

/-- The analogous negative-channel germ. -/
theorem completedNativeCenteredNegativeChiralResponse_eventuallyEq :
    completedNativeCenteredNegativeChiralResponse =ᶠ[nhds 0]
      (fun z => Complex.I / 4 -
        completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z / 2) := by
  have hnonzero : ∀ᶠ z in nhds (0 : ℂ),
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hnonzero] with z hzF
  exact completedNativeCenteredNegativeChiralResponse_eq hzF

/-- Taylor coefficient of the rotated positive scalar channel. -/
def completedNativeCenteredPositiveChiralTaylorCoefficient
    (order : ℕ) : ℂ :=
  iteratedDeriv order completedNativeCenteredPositiveChiralResponse 0 /
    order.factorial

/-- Taylor coefficient of the rotated negative scalar channel. -/
def completedNativeCenteredNegativeChiralTaylorCoefficient
    (order : ℕ) : ℂ :=
  iteratedDeriv order completedNativeCenteredNegativeChiralResponse 0 /
    order.factorial

/-- Every nonconstant positive chiral coefficient is exactly one half of the
completed response coefficient. -/
theorem completedNativeCenteredPositiveChiralTaylorCoefficient_eq_half
    {order : ℕ} (horder : 0 < order) :
    completedNativeCenteredPositiveChiralTaylorCoefficient order =
      completedNativeGreenResponseTaylorCoefficient order / 2 := by
  unfold completedNativeCenteredPositiveChiralTaylorCoefficient
    completedNativeGreenResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order
    completedNativeCenteredPositiveChiralResponse_eventuallyEq]
  rw [iteratedDeriv_const_add horder]
  simp only [div_eq_mul_inv, iteratedDeriv_mul_const_field]
  ring

/-- Every nonconstant negative chiral coefficient is the opposite half of the
completed response coefficient. -/
theorem completedNativeCenteredNegativeChiralTaylorCoefficient_eq_neg_half
    {order : ℕ} (horder : 0 < order) :
    completedNativeCenteredNegativeChiralTaylorCoefficient order =
      -completedNativeGreenResponseTaylorCoefficient order / 2 := by
  unfold completedNativeCenteredNegativeChiralTaylorCoefficient
    completedNativeGreenResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order
    completedNativeCenteredNegativeChiralResponse_eventuallyEq]
  rw [iteratedDeriv_const_sub horder]
  change
    iteratedDeriv order
          (fun z => -(completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion z / 2)) 0 /
        order.factorial = _
  rw [iteratedDeriv_fun_neg]
  simp only [div_eq_mul_inv, iteratedDeriv_mul_const_field]
  ring

/-- Odd positive chiral coefficients are positive halves of the canonical
moments as scalars; this statement itself carries no sign assertion. -/
theorem completedNativeCenteredPositiveChiralTaylorCoefficient_odd
    (n : ℕ) :
    completedNativeCenteredPositiveChiralTaylorCoefficient (2 * n + 1) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) / 2 := by
  rw [completedNativeCenteredPositiveChiralTaylorCoefficient_eq_half (by omega),
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]

/-- Odd negative chiral coefficients are the opposite halves.  Thus the
positivity of the original negative Gram kernel is not preserved by the
center-pinned odd Taylor extraction. -/
theorem completedNativeCenteredNegativeChiralTaylorCoefficient_odd
    (n : ℕ) :
    completedNativeCenteredNegativeChiralTaylorCoefficient (2 * n + 1) =
      -(canonicalCompletedNativeLogDerivativeMoment n : ℂ) / 2 := by
  rw [completedNativeCenteredNegativeChiralTaylorCoefficient_eq_neg_half (by omega),
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]

/-- Hankelization of the rotated positive chiral Taylor channel. -/
def completedNativeCenteredPositiveEvenChiralContribution
    (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (completedNativeCenteredPositiveChiralTaylorCoefficient
      (2 * ((i : ℕ) + (j : ℕ)) + 1)).re

/-- Hankelization of the rotated negative chiral Taylor channel. -/
def completedNativeCenteredNegativeEvenChiralContribution
    (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (completedNativeCenteredNegativeChiralTaylorCoefficient
      (2 * ((i : ℕ) + (j : ℕ)) + 1)).re

/-- Shifted Hankelization of the rotated positive chiral channel. -/
def completedNativeCenteredPositiveOddChiralContribution
    (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (completedNativeCenteredPositiveChiralTaylorCoefficient
      (2 * ((i : ℕ) + (j : ℕ) + 1) + 1)).re

/-- Shifted Hankelization of the rotated negative chiral channel. -/
def completedNativeCenteredNegativeOddChiralContribution
    (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (completedNativeCenteredNegativeChiralTaylorCoefficient
      (2 * ((i : ℕ) + (j : ℕ) + 1) + 1)).re

/-- The extracted positive even contribution is exactly half of the canonical
Hankel matrix. -/
theorem completedNativeCenteredPositiveEvenChiralContribution_eq_half_hankel
    (N : ℕ) :
    completedNativeCenteredPositiveEvenChiralContribution N =
      (2 : ℝ)⁻¹ • hankelGram canonicalCompletedNativeLogDerivativeMoment N := by
  ext i j
  rw [completedNativeCenteredPositiveEvenChiralContribution,
    completedNativeCenteredPositiveChiralTaylorCoefficient_odd]
  simp [hankelGram]
  ring

/-- The extracted negative even contribution is the opposite half. -/
theorem completedNativeCenteredNegativeEvenChiralContribution_eq_neg_half_hankel
    (N : ℕ) :
    completedNativeCenteredNegativeEvenChiralContribution N =
      -(2 : ℝ)⁻¹ • hankelGram canonicalCompletedNativeLogDerivativeMoment N := by
  ext i j
  rw [completedNativeCenteredNegativeEvenChiralContribution,
    completedNativeCenteredNegativeChiralTaylorCoefficient_odd]
  simp [hankelGram]
  ring

/-- The positive shifted contribution is half of the shifted Hankel matrix. -/
theorem completedNativeCenteredPositiveOddChiralContribution_eq_half_shiftedHankel
    (N : ℕ) :
    completedNativeCenteredPositiveOddChiralContribution N =
      (2 : ℝ)⁻¹ • shiftedHankel canonicalCompletedNativeLogDerivativeMoment N := by
  ext i j
  rw [completedNativeCenteredPositiveOddChiralContribution,
    completedNativeCenteredPositiveChiralTaylorCoefficient_odd]
  simp [shiftedHankel]
  ring

/-- The negative shifted contribution is the opposite half. -/
theorem completedNativeCenteredNegativeOddChiralContribution_eq_neg_half_shiftedHankel
    (N : ℕ) :
    completedNativeCenteredNegativeOddChiralContribution N =
      -(2 : ℝ)⁻¹ • shiftedHankel canonicalCompletedNativeLogDerivativeMoment N := by
  ext i j
  rw [completedNativeCenteredNegativeOddChiralContribution,
    completedNativeCenteredNegativeChiralTaylorCoefficient_odd]
  simp [shiftedHankel]
  ring

/-- Even-parity all-order Loewner defect of the expanded chiral signature.
The order `2 * (i + j) + 1` includes the derivative removed by division by the
spectral separation. -/
def canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect
    (M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient M
      (2 * ((i : ℕ) + (j : ℕ)) + 1)).re

/-- Odd-parity all-order Loewner defect.  The extra shift is the Stieltjes
localizing tower rather than an independently normalized channel. -/
def canonicalCompletedC3ExpandedStructuralOddLoewnerDefect
    (M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient M
      (2 * ((i : ℕ) + (j : ℕ) + 1) + 1)).re

/-- The regularized even chiral defect is exactly the canonical Hankel
matrix, entry by entry and at every cutoff. -/
theorem canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel
    (M N : ℕ) :
    canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect M N =
      hankelGram canonicalCompletedNativeLogDerivativeMoment N := by
  ext i j
  rw [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect,
    canonicalCompletedC3ExpandedStructuralSignature_odd_eq_canonicalMoment]
  simp [hankelGram]

/-- The regularized odd chiral defect is exactly the shifted canonical Hankel
matrix. -/
theorem canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel
    (M N : ℕ) :
    canonicalCompletedC3ExpandedStructuralOddLoewnerDefect M N =
      shiftedHankel canonicalCompletedNativeLogDerivativeMoment N := by
  ext i j
  rw [canonicalCompletedC3ExpandedStructuralOddLoewnerDefect,
    canonicalCompletedC3ExpandedStructuralSignature_odd_eq_canonicalMoment]
  simp [shiftedHankel]

/-- The expanded even Loewner defect is literally the positive rotated
coefficient block minus the negative rotated coefficient block. -/
theorem canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_chiral_sub
    (M N : ℕ) :
    canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect M N =
      completedNativeCenteredPositiveEvenChiralContribution N -
        completedNativeCenteredNegativeEvenChiralContribution N := by
  rw [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel,
    completedNativeCenteredPositiveEvenChiralContribution_eq_half_hankel,
    completedNativeCenteredNegativeEvenChiralContribution_eq_neg_half_hankel]
  ext i j
  simp
  ring

/-- The same exact signed decomposition in the shifted parity sector. -/
theorem canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_chiral_sub
    (M N : ℕ) :
    canonicalCompletedC3ExpandedStructuralOddLoewnerDefect M N =
      completedNativeCenteredPositiveOddChiralContribution N -
        completedNativeCenteredNegativeOddChiralContribution N := by
  rw [canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel,
    completedNativeCenteredPositiveOddChiralContribution_eq_half_shiftedHankel,
    completedNativeCenteredNegativeOddChiralContribution_eq_neg_half_shiftedHankel]
  ext i j
  simp
  ring

/-- Differentiating the constant total chiral energy kills its even-sector
coefficient matrix exactly. -/
theorem completedNativeCenteredEvenChiralContributions_add_eq_zero
    (N : ℕ) :
    completedNativeCenteredPositiveEvenChiralContribution N +
      completedNativeCenteredNegativeEvenChiralContribution N = 0 := by
  rw [completedNativeCenteredPositiveEvenChiralContribution_eq_half_hankel,
    completedNativeCenteredNegativeEvenChiralContribution_eq_neg_half_hankel]
  ext i j
  simp

/-- The shifted coefficient matrices cancel in the unsigned sum as well. -/
theorem completedNativeCenteredOddChiralContributions_add_eq_zero
    (N : ℕ) :
    completedNativeCenteredPositiveOddChiralContribution N +
      completedNativeCenteredNegativeOddChiralContribution N = 0 := by
  rw [completedNativeCenteredPositiveOddChiralContribution_eq_half_shiftedHankel,
    completedNativeCenteredNegativeOddChiralContribution_eq_neg_half_shiftedHankel]
  ext i j
  simp

/-- Exact head-tail completion makes the even all-order chiral defect
independent of the carrier cutoff. -/
theorem canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_cutoff_independent
    (M K N : ℕ) :
    canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect M N =
      canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect K N := by
  rw [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel,
    canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel]

/-- The shifted all-order chiral defect is cutoff-independent as well. -/
theorem canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_cutoff_independent
    (M K N : ℕ) :
    canonicalCompletedC3ExpandedStructuralOddLoewnerDefect M N =
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect K N := by
  rw [canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel,
    canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel]

/-- Closed Loewner dominance of the regularized expanded chiral signature in
both parity sectors. -/
def CanonicalCompletedC3ExpandedStructuralChiralDominance : Prop :=
  ∀ N : ℕ,
    (canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect 0 N).PosSemidef ∧
      (canonicalCompletedC3ExpandedStructuralOddLoewnerDefect 0 N).PosSemidef

/-- Strict all-order chiral dominance, including absence of a finite null
direction in either parity sector. -/
def CanonicalCompletedC3ExpandedStructuralStrictChiralDominance : Prop :=
  ∀ N : ℕ,
    (canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect 0 N).PosDef ∧
      (canonicalCompletedC3ExpandedStructuralOddLoewnerDefect 0 N).PosDef

/-- Closed Loewner dominance written directly as `K₊ - K₋ ⪰ 0` for the
two centered chiral coefficient towers. -/
def CanonicalCompletedNativeCenteredChiralCoefficientDominance : Prop :=
  ∀ N : ℕ,
    (completedNativeCenteredPositiveEvenChiralContribution N -
        completedNativeCenteredNegativeEvenChiralContribution N).PosSemidef ∧
      (completedNativeCenteredPositiveOddChiralContribution N -
        completedNativeCenteredNegativeOddChiralContribution N).PosSemidef

/-- Strict form of the same coefficient-level Loewner dominance. -/
def CanonicalCompletedNativeCenteredStrictChiralCoefficientDominance : Prop :=
  ∀ N : ℕ,
    (completedNativeCenteredPositiveEvenChiralContribution N -
        completedNativeCenteredNegativeEvenChiralContribution N).PosDef ∧
      (completedNativeCenteredPositiveOddChiralContribution N -
        completedNativeCenteredNegativeOddChiralContribution N).PosDef

/-- The scalar and expanded structural spellings of closed chiral dominance
coincide exactly. -/
theorem
    canonicalCompletedNativeCenteredChiralCoefficientDominance_iff_expanded :
    CanonicalCompletedNativeCenteredChiralCoefficientDominance ↔
      CanonicalCompletedC3ExpandedStructuralChiralDominance := by
  constructor <;> intro h N
  · simpa [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_chiral_sub,
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_chiral_sub]
      using h N
  · simpa [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_chiral_sub,
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_chiral_sub]
      using h N

/-- The strict scalar and expanded structural dominance gates coincide. -/
theorem
    canonicalCompletedNativeCenteredStrictChiralCoefficientDominance_iff_expanded :
    CanonicalCompletedNativeCenteredStrictChiralCoefficientDominance ↔
      CanonicalCompletedC3ExpandedStructuralStrictChiralDominance := by
  constructor <;> intro h N
  · simpa [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_chiral_sub,
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_chiral_sub]
      using h N
  · simpa [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_chiral_sub,
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_chiral_sub]
      using h N

/-- Closed chiral dominance is exactly the semidefinite completed-native
Stieltjes pair. -/
theorem
    canonicalCompletedC3ExpandedStructuralChiralDominance_iff_stieltjesPosSemidefinite :
    CanonicalCompletedC3ExpandedStructuralChiralDominance ↔
      CanonicalCompletedNativeStieltjesPosSemidefinite := by
  constructor
  · intro h N
    simpa [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel,
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel]
      using h N
  · intro h N
    simpa [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel,
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel]
      using h N

/-- Strict all-order chiral dominance is exactly the momental gate consumed by
the canonical completed-native Jacobi construction. -/
theorem
    canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity :
    CanonicalCompletedC3ExpandedStructuralStrictChiralDominance ↔
      CanonicalCompletedNativeStieltjesPositivity := by
  constructor
  · intro h N
    simpa [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel,
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel]
      using h N
  · intro h N
    simpa [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel,
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel]
      using h N

/-- The exact strength audit: strict chiral dominance consists of closed
dominance plus finite-section nondegeneracy. -/
theorem
    canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_dominance_and_nondegenerate :
    CanonicalCompletedC3ExpandedStructuralStrictChiralDominance ↔
      CanonicalCompletedC3ExpandedStructuralChiralDominance ∧
        CanonicalCompletedNativeHankelPairNondegenerate := by
  rw [canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity,
    canonicalCompletedC3ExpandedStructuralChiralDominance_iff_stieltjesPosSemidefinite,
    canonicalCompletedNativeStieltjesPositivity_iff_posSemidefinite_and_nondegenerate]

/-- At the first nonempty section, the regularized chiral dominance gate is
literally positivity of the first two canonical moments. -/
theorem canonicalCompletedC3ExpandedStructuralStrictChiralDominance_one_iff :
    (canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect 0 1).PosDef ∧
        (canonicalCompletedC3ExpandedStructuralOddLoewnerDefect 0 1).PosDef ↔
      0 < canonicalCompletedNativeLogDerivativeMoment 0 ∧
        0 < canonicalCompletedNativeLogDerivativeMoment 1 := by
  rw [canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel,
    canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel]
  exact canonicalCompletedNativeHankelPair_one_posDef_iff

end

end CarrySelfAdjointOperator

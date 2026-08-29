import CarrySelfAdjointOperator.CompletedNativeTfvdAllOrderTaylorCompletion
import CarrySelfAdjointOperator.CompletedNativeProductMomentCenter
import Mathlib.Tactic

/-!
# Pointwise moment audit for the enriched TFVD Taylor carrier

The polarized coefficient equation is first reduced to its unique pointwise
solution.  For the concrete enriched TFVD Taylor family, the resulting Gram
entries are then opened into the retained ordinary and logarithmic channels.
This keeps the normalization question visible at every parity block.
-/

open scoped ComplexOrder InnerProductSpace lp ENNReal NNReal

namespace CarrySelfAdjointOperator

noncomputable section

/-- A raw vector family satisfies the division-free coefficient recurrence
exactly when every one of its Gram entries is the canonical polarized moment
coefficient. -/
theorem hasPolarizedCoefficientVectorEquation_iff_pointwise
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {rawJet : ℕ → E} :
    HasPolarizedCoefficientVectorEquation moments rawJet ↔
      ∀ p q : ℕ,
        inner ℂ (rawJet p) (rawJet q) =
          polarizedGreenMomentCoefficient moments p q := by
  constructor
  · intro hcoeff p q
    exact polarizedGreenCoefficient_unique hcoeff p q
  · intro hpoint
    simpa [HasPolarizedCoefficientVectorEquation, hpoint] using
      polarizedGreenMomentCoefficient_coefficientEquation moments

/-- The concrete enriched Gram is the sum of the ordinary and logarithmic
channel Grams; no channel has been projected out. -/
theorem inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet
    (p q : ℕ) :
    inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet p)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet q) =
      inner ℂ
          (canonicalCompletedNativeTfvdTaylorCoefficientState p)
          (canonicalCompletedNativeTfvdTaylorCoefficientState q) +
        inner ℂ
          (canonicalCompletedNativeTfvdLogTaylorCoefficientState p)
          (canonicalCompletedNativeTfvdLogTaylorCoefficientState q) := by
  rfl

/-- Coordinate expansion of the ordinary Taylor-channel Gram. -/
theorem inner_canonicalCompletedNativeTfvdTaylorCoefficientState_eq_tsum
    (p q : ℕ) :
    inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState p)
        (canonicalCompletedNativeTfvdTaylorCoefficientState q) =
      ∑' n : ℕ,
        (starRingEnd ℂ) (nativeDirichletSlopeTaylorCoefficient p n) *
          nativeDirichletSlopeTaylorCoefficient q n := by
  rw [lp.inner_eq_tsum]
  congr 1
  funext n
  simp [RCLike.inner_apply, mul_comm]

/-- Coordinate expansion of the logarithmic Taylor-channel Gram. -/
theorem inner_canonicalCompletedNativeTfvdLogTaylorCoefficientState_eq_tsum
    (p q : ℕ) :
    inner ℂ
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState p)
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState q) =
      ∑' n : ℕ,
        (starRingEnd ℂ) (nativeLogDirichletSlopeTaylorCoefficient p n) *
          nativeLogDirichletSlopeTaylorCoefficient q n := by
  rw [lp.inner_eq_tsum]
  congr 1
  funext n
  simp [RCLike.inner_apply, mul_comm]

/-- Fully expanded pointwise target.  The right side is the completed-native
moment coefficient; the left side is the two explicit native slope series. -/
theorem enrichedTfvdTaylorEquation_iff_pointwiseSeries :
    HasPolarizedCoefficientVectorEquation
        canonicalCompletedNativeLogDerivativeMoment
        canonicalCompletedNativeTfvdEnrichedTaylorRawJet ↔
      ∀ p q : ℕ,
        (∑' n : ℕ,
            (starRingEnd ℂ) (nativeDirichletSlopeTaylorCoefficient p n) *
              nativeDirichletSlopeTaylorCoefficient q n) +
          (∑' n : ℕ,
            (starRingEnd ℂ)
                (nativeLogDirichletSlopeTaylorCoefficient p n) *
              nativeLogDirichletSlopeTaylorCoefficient q n) =
          polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment p q := by
  rw [hasPolarizedCoefficientVectorEquation_iff_pointwise]
  constructor <;> intro h p q
  · simpa [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet,
      inner_canonicalCompletedNativeTfvdTaylorCoefficientState_eq_tsum,
      inner_canonicalCompletedNativeTfvdLogTaylorCoefficientState_eq_tsum] using
      h p q
  · simpa [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet,
      inner_canonicalCompletedNativeTfvdTaylorCoefficientState_eq_tsum,
      inner_canonicalCompletedNativeTfvdLogTaylorCoefficientState_eq_tsum] using
      h p q

/-! ## Parity orthogonality required by the real HP carrier -/

@[simp] theorem nativeCriticalDirichletAmplitude_eq_realRpow (m : ℕ) :
    nativeCriticalDirichletAmplitude m =
      (((m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  exact natDirichletTerm_half_eq_realRpow m

/-- Real amplitude left after removing the universal Taylor phase. -/
def nativeDirichletSlopeTaylorRealCoefficient (order n : ℕ) : ℝ :=
  (((n + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.log ((n + 2 : ℕ) : ℝ) ^ order -
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.log ((n + 1 : ℕ) : ℝ) ^ order) /
    order.factorial

theorem nativeDirichletSlopeTaylorCoefficient_eq_phase_mul_real
    (order n : ℕ) :
    nativeDirichletSlopeTaylorCoefficient order n =
      (-Complex.I) ^ order *
        (nativeDirichletSlopeTaylorRealCoefficient order n : ℂ) := by
  unfold nativeDirichletSlopeTaylorCoefficient
    nativeDirichletSlopeTaylorRealCoefficient
  rw [nativeCriticalDirichletAmplitude_eq_realRpow,
    nativeCriticalDirichletAmplitude_eq_realRpow]
  push_cast
  simp only [mul_pow]
  field_simp [Nat.factorial_ne_zero]

theorem neg_I_pow_even (order : ℕ) :
    (-Complex.I) ^ (2 * order) =
      (↑((-1 : ℝ) ^ order) : ℂ) := by
  rw [pow_mul]
  norm_num [Complex.I_sq]

theorem neg_I_pow_odd (order : ℕ) :
    (-Complex.I) ^ (2 * order + 1) =
      (↑((-1 : ℝ) ^ order) : ℂ) * (-Complex.I) := by
  rw [pow_add, neg_I_pow_even]
  simp

@[simp] theorem nativeDirichletSlopeTaylorCoefficient_even_im
    (order n : ℕ) :
    (nativeDirichletSlopeTaylorCoefficient (2 * order) n).im = 0 := by
  rw [nativeDirichletSlopeTaylorCoefficient_eq_phase_mul_real,
    neg_I_pow_even]
  have hsignIm : ((↑((-1 : ℝ) ^ order) : ℂ)).im = 0 :=
    Complex.ofReal_im _
  have hcoefficientIm :
      ((nativeDirichletSlopeTaylorRealCoefficient
        (2 * order) n : ℂ)).im = 0 := Complex.ofReal_im _
  rw [Complex.mul_im, hsignIm, hcoefficientIm]
  ring

@[simp] theorem nativeDirichletSlopeTaylorCoefficient_odd_re
    (order n : ℕ) :
    (nativeDirichletSlopeTaylorCoefficient (2 * order + 1) n).re = 0 := by
  rw [nativeDirichletSlopeTaylorCoefficient_eq_phase_mul_real,
    neg_I_pow_odd]
  have hsignIm : ((↑((-1 : ℝ) ^ order) : ℂ)).im = 0 :=
    Complex.ofReal_im _
  have hcoefficientIm :
      ((nativeDirichletSlopeTaylorRealCoefficient
        (2 * order + 1) n : ℂ)).im = 0 := Complex.ofReal_im _
  have hIre : (-Complex.I).re = 0 := by norm_num
  rw [Complex.mul_re, Complex.mul_re, Complex.mul_im,
    hsignIm, hcoefficientIm, hIre]
  ring

@[simp] theorem nativeLogDirichletSlopeTaylorCoefficient_even_im
    (order n : ℕ) :
    (nativeLogDirichletSlopeTaylorCoefficient (2 * order) n).im = 0 := by
  rw [nativeLogDirichletSlopeTaylorCoefficient_eq_succ]
  simp [Complex.mul_im]

@[simp] theorem nativeLogDirichletSlopeTaylorCoefficient_odd_re
    (order n : ℕ) :
    (nativeLogDirichletSlopeTaylorCoefficient (2 * order + 1) n).re = 0 := by
  rw [nativeLogDirichletSlopeTaylorCoefficient_eq_succ]
  have him := nativeDirichletSlopeTaylorCoefficient_even_im (order + 1) n
  have hindex : 2 * order + 1 + 1 = 2 * (order + 1) := by omega
  rw [hindex]
  simp [Complex.mul_re, him]

theorem re_inner_canonicalCompletedNativeTfvdTaylor_even_odd
    (i j : ℕ) :
    (inner ℂ
      (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * i))
      (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * j + 1))).re =
        0 := by
  rw [lp.inner_eq_tsum,
    Complex.re_tsum (lp.summable_inner
      (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * i))
      (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * j + 1)))]
  simp [RCLike.inner_apply, Complex.mul_re]

theorem re_inner_canonicalCompletedNativeTfvdLogTaylor_even_odd
    (i j : ℕ) :
    (inner ℂ
      (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * i))
      (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * j + 1))).re =
        0 := by
  rw [lp.inner_eq_tsum,
    Complex.re_tsum (lp.summable_inner
      (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * i))
      (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * j + 1)))]
  simp [RCLike.inner_apply, Complex.mul_re]

theorem re_inner_canonicalCompletedNativeTfvdEnrichedTaylor_even_odd
    (i j : ℕ) :
    (inner ℂ
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * i))
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * j + 1))).re =
        0 := by
  rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet,
    Complex.add_re,
    re_inner_canonicalCompletedNativeTfvdTaylor_even_odd,
    re_inner_canonicalCompletedNativeTfvdLogTaylor_even_odd]
  simp

theorem re_inner_canonicalCompletedNativeTfvdEnrichedTaylor_odd_even
    (i j : ℕ) :
    (inner ℂ
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * i + 1))
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * j))).re =
        0 := by
  have hsymm :
      (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * i + 1))
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * j))).re =
      (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * j))
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet
          (2 * i + 1))).re := by
    have h := congrArg Complex.re
      (inner_conj_symm
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * i + 1))
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * j)))
    simpa only [map_star, Complex.conj_re] using h.symm
  calc
    _ = (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * j))
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet
          (2 * i + 1))).re := hsymm
    _ = 0 :=
      re_inner_canonicalCompletedNativeTfvdEnrichedTaylor_even_odd j i

/-- Pointwise form of the remaining coefficient gate after opening both
retained TFVD channels. -/
theorem enrichedTfvdTaylorEquation_iff_pointwiseChannelSum :
    HasPolarizedCoefficientVectorEquation
        canonicalCompletedNativeLogDerivativeMoment
        canonicalCompletedNativeTfvdEnrichedTaylorRawJet ↔
      ∀ p q : ℕ,
        inner ℂ
            (canonicalCompletedNativeTfvdTaylorCoefficientState p)
            (canonicalCompletedNativeTfvdTaylorCoefficientState q) +
          inner ℂ
            (canonicalCompletedNativeTfvdLogTaylorCoefficientState p)
            (canonicalCompletedNativeTfvdLogTaylorCoefficientState q) =
          polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment p q := by
  rw [hasPolarizedCoefficientVectorEquation_iff_pointwise]
  constructor <;> intro h p q
  · simpa [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet] using h p q
  · simpa [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet] using h p q

/-- The even-even block required by the coefficient equation. -/
theorem enrichedTfvdTaylorEquation_even_even
    (hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet)
    (i j : ℕ) :
    inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * i))
        (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * j)) +
      inner ℂ
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * i))
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * j)) =
      (canonicalCompletedNativeLogDerivativeMoment (i + j) : ℂ) := by
  have h := (enrichedTfvdTaylorEquation_iff_pointwiseChannelSum.mp hcoeff)
    (2 * i) (2 * j)
  simpa using h

/-- The odd-odd block required by the coefficient equation. -/
theorem enrichedTfvdTaylorEquation_odd_odd
    (hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet)
    (i j : ℕ) :
    inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * i + 1))
        (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * j + 1)) +
      inner ℂ
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * i + 1))
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * j + 1)) =
      (canonicalCompletedNativeLogDerivativeMoment (i + j + 1) : ℂ) := by
  have h := (enrichedTfvdTaylorEquation_iff_pointwiseChannelSum.mp hcoeff)
    (2 * i + 1) (2 * j + 1)
  simpa using h

/-- The even-odd block must vanish before taking real parts. -/
theorem enrichedTfvdTaylorEquation_even_odd
    (hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet)
    (i j : ℕ) :
    inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * i))
        (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * j + 1)) +
      inner ℂ
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * i))
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * j + 1)) =
      0 := by
  have h := (enrichedTfvdTaylorEquation_iff_pointwiseChannelSum.mp hcoeff)
    (2 * i) (2 * j + 1)
  simpa using h

/-- The odd-even block must vanish before taking real parts. -/
theorem enrichedTfvdTaylorEquation_odd_even
    (hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet)
    (i j : ℕ) :
    inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * i + 1))
        (canonicalCompletedNativeTfvdTaylorCoefficientState (2 * j)) +
      inner ℂ
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * i + 1))
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState (2 * j)) =
      0 := by
  have h := (enrichedTfvdTaylorEquation_iff_pointwiseChannelSum.mp hcoeff)
    (2 * i + 1) (2 * j)
  simpa using h

/-- The first diagonal identity demanded from the current enriched source
carrier. -/
theorem enrichedTfvdTaylorEquation_zero_zero
    (hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet) :
    inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState 0)
        (canonicalCompletedNativeTfvdTaylorCoefficientState 0) +
      inner ℂ
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState 0)
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState 0) =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simpa using enrichedTfvdTaylorEquation_even_even hcoeff 0 0

/-- The first mixed identity demanded from the current enriched source
carrier. -/
theorem enrichedTfvdTaylorEquation_zero_one
    (hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet) :
    inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState 0)
        (canonicalCompletedNativeTfvdTaylorCoefficientState 1) +
      inner ℂ
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState 0)
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState 1) =
      0 := by
  simpa using enrichedTfvdTaylorEquation_even_odd hcoeff 0 0

@[simp] theorem canonicalCompletedNativeTfvdLogTaylorCoefficientState_zero :
    canonicalCompletedNativeTfvdLogTaylorCoefficientState 0 =
      canonicalCompletedC3LogJetState (1 / 2 : ℂ) (by norm_num) := by
  rw [canonicalCompletedNativeTfvdLogTaylorCoefficientState,
    canonicalCompletedNativeTfvdTaylorCoefficientState_one]
  simp [smul_smul]

/-- The first concrete diagonal Gram is exactly the ordinary completed C3
source energy plus its log-jet source energy. -/
theorem inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero :
    inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0) =
      inner ℂ
          (canonicalCompletedC3DirichletGradientState
            (1 / 2 : ℂ) (by norm_num))
          (canonicalCompletedC3DirichletGradientState
            (1 / 2 : ℂ) (by norm_num)) +
        inner ℂ
          (canonicalCompletedC3LogJetState
            (1 / 2 : ℂ) (by norm_num))
          (canonicalCompletedC3LogJetState
            (1 / 2 : ℂ) (by norm_num)) := by
  rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet]
  simp

/-- The zeroth instance of the remaining even diagonal identity, stated
without the stronger complex coefficient recurrence. -/
theorem enrichedTfvdTaylorEvenDiagonalMoments_zero
    (heven : ∀ i j : ℕ,
      (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * i))
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * j))).re =
          canonicalCompletedNativeLogDerivativeMoment (i + j)) :
    (inner ℂ
        (canonicalCompletedC3DirichletGradientState
          (1 / 2 : ℂ) (by norm_num))
        (canonicalCompletedC3DirichletGradientState
          (1 / 2 : ℂ) (by norm_num))).re +
      (inner ℂ
        (canonicalCompletedC3LogJetState
          (1 / 2 : ℂ) (by norm_num))
        (canonicalCompletedC3LogJetState
          (1 / 2 : ℂ) (by norm_num))).re =
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hzero := heven 0 0
  rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero,
    Complex.add_re] at hzero
  simpa using hzero

/-- Expanded zeroth diagonal requirement.  The source Gram would have to
reproduce the complete second product jet, including its mixed completion
factor/native-height channel. -/
theorem enrichedTfvdTaylorEvenDiagonalMoments_zero_eq_productJet
    (heven : ∀ i j : ℕ,
      (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * i))
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * j))).re =
          canonicalCompletedNativeLogDerivativeMoment (i + j)) :
    inner ℂ
        (canonicalCompletedC3DirichletGradientState
          (1 / 2 : ℂ) (by norm_num))
        (canonicalCompletedC3DirichletGradientState
          (1 / 2 : ℂ) (by norm_num)) +
      inner ℂ
        (canonicalCompletedC3LogJetState
          (1 / 2 : ℂ) (by norm_num))
        (canonicalCompletedC3LogJetState
          (1 / 2 : ℂ) (by norm_num)) =
      -(iteratedDeriv 2 nativeXiCompletionFactor 0 * nativeHeightScalar 0 +
          2 * deriv nativeXiCompletionFactor 0 * deriv nativeHeightScalar 0 +
          nativeXiCompletionFactor 0 * iteratedDeriv 2 nativeHeightScalar 0) /
        (2 * nativeXiCompletionFactor 0 * nativeHeightScalar 0) := by
  have hzero := heven 0 0
  have hcomplex :
      inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0) =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
    have hnorm :
        ‖canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0‖ ^ 2 =
          canonicalCompletedNativeLogDerivativeMoment 0 := by
      rw [inner_self_eq_norm_sq_to_K] at hzero
      norm_num [pow_two, Complex.mul_re] at hzero
      simpa [pow_two] using hzero
    rw [inner_self_eq_norm_sq_to_K]
    calc
      (↑‖canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0‖ : ℂ) ^ 2 =
          (↑(‖canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0‖ ^ 2) : ℂ) :=
        (Complex.ofReal_pow _ _).symm
      _ = (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) :=
        congrArg Complex.ofReal hnorm
  rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero]
    at hcomplex
  calc
    _ = (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := hcomplex
    _ = _ := canonicalCompletedNativeLogDerivativeMoment_zero_eq_productJet

/-! ## Direct real HP reduction -/

/-- For the actual real HP carrier, opposite parities are already orthogonal.
Consequently only the two diagonal Hankel identifications remain.  This
constructor deliberately avoids the stronger complex coefficient equation. -/
theorem completedNativeRealHPCarrierCertificate_of_enrichedTfvdTaylorDiagonalMoments
    (heven : ∀ i j : ℕ,
      (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * i))
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * j))).re =
          canonicalCompletedNativeLogDerivativeMoment (i + j))
    (hodd : ∀ i j : ℕ,
      (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * i + 1))
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet
          (2 * j + 1))).re =
          canonicalCompletedNativeLogDerivativeMoment (i + j + 1)) :
    letI : InnerProductSpace ℝ
        CanonicalCompletedNativeTfvdEnrichedTaylorCarrier :=
      InnerProductSpace.rclikeToReal ℂ
        CanonicalCompletedNativeTfvdEnrichedTaylorCarrier
    CompletedNativeRealHPCarrierCertificate
      (polarizedCoefficientParityJet
        canonicalCompletedNativeTfvdEnrichedTaylorRawJet) := by
  letI : InnerProductSpace ℝ
      CanonicalCompletedNativeTfvdEnrichedTaylorCarrier :=
    InnerProductSpace.rclikeToReal ℂ
      CanonicalCompletedNativeTfvdEnrichedTaylorCarrier
  refine
    { momentKernel := ?_
      evenIndependent :=
        canonicalCompletedNativeTfvdEnrichedTaylorEven_linearIndependent
          |>.restrict_scalars' ℝ
      oddIndependent :=
        canonicalCompletedNativeTfvdEnrichedTaylorOdd_linearIndependent
          |>.restrict_scalars' ℝ }
  intro i j
  change greenWronskianMomentKernel
      canonicalCompletedNativeLogDerivativeMoment i j =
    (inner ℂ
      (polarizedCoefficientParityJet
        canonicalCompletedNativeTfvdEnrichedTaylorRawJet i)
      (polarizedCoefficientParityJet
        canonicalCompletedNativeTfvdEnrichedTaylorRawJet j)).re
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simpa [greenWronskianMomentKernel,
            polarizedCoefficientParityJet] using (heven i j).symm
      | inr j =>
          simpa [greenWronskianMomentKernel,
            polarizedCoefficientParityJet] using
            (re_inner_canonicalCompletedNativeTfvdEnrichedTaylor_even_odd
              i j).symm
  | inr i =>
      cases j with
      | inl j =>
          simpa [greenWronskianMomentKernel,
            polarizedCoefficientParityJet] using
            (re_inner_canonicalCompletedNativeTfvdEnrichedTaylor_odd_even
              i j).symm
      | inr j =>
          simpa [greenWronskianMomentKernel,
            polarizedCoefficientParityJet] using (hodd i j).symm

end

end CarrySelfAdjointOperator

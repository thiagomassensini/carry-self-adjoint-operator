import CarrySelfAdjointOperator.CompletedNativeCentralChiralVariation
import CPFormal.Analytic.CpGenuineTiltProductRule
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Central first sensitivity of the carry tilt

The C3 carry tilt vanishes at the self-dual displacement `delta = 0`, but its
first variation does not.  This file computes that variation exactly and
proves its strict sign before any Green, Hankel, or spectral readout.

The result is deliberately kept at the geometric product-rule level.  The
critical weighted tilt is only one channel of the full native bracket; the
critical-carrier curvature and cross channels are not discarded.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Exact logarithmic first sensitivity of the radius-one carry tilt. -/
def carryTiltThreeFirstSensitivity (center : ℝ) : ℝ :=
  -Real.log (center - 1) - Real.log (center + 1) +
    2 * Real.log center

/-- The first variation of the C3 tilt at the self-dual displacement is the
centered logarithmic curvature. -/
theorem hasDerivAt_cpTilt_three_zero
    {center : ℝ} (hcenter : 1 < center) :
    HasDerivAt (fun delta : ℝ ↦ cpTilt 3 delta center)
      (carryTiltThreeFirstSensitivity center) 0 := by
  have hleft : HasDerivAt (fun delta : ℝ ↦ (center - 1) ^ (-delta))
      (-Real.log (center - 1)) 0 := by
    simpa using
      (hasDerivAt_neg' (0 : ℝ)).const_rpow (by linarith : 0 < center - 1)
  have hright : HasDerivAt (fun delta : ℝ ↦ (center + 1) ^ (-delta))
      (-Real.log (center + 1)) 0 := by
    simpa using
      (hasDerivAt_neg' (0 : ℝ)).const_rpow (by linarith : 0 < center + 1)
  have hmiddle : HasDerivAt (fun delta : ℝ ↦ center ^ (-delta))
      (-Real.log center) 0 := by
    simpa using
      (hasDerivAt_neg' (0 : ℝ)).const_rpow (by linarith : 0 < center)
  rw [show (fun delta : ℝ ↦ cpTilt 3 delta center) =
      (fun delta : ℝ ↦
        (center - 1) ^ (-delta) + (center + 1) ^ (-delta) -
          2 * center ^ (-delta)) by
    funext delta
    rw [cpTilt_three_eq_cpPairTilt_one]
    simp [cpPairTilt]]
  refine ((hleft.add hright).sub (hmiddle.const_mul 2)).congr_deriv ?_
  unfold carryTiltThreeFirstSensitivity
  ring

/-- The logarithmic first sensitivity is strictly positive at every
radius-one admissible center. -/
theorem carryTiltThreeFirstSensitivity_pos
    {center : ℝ} (hcenter : 1 < center) :
    0 < carryTiltThreeFirstSensitivity center := by
  have hleft : center - 1 ∈ Set.Ioi (0 : ℝ) := by
    exact sub_pos.mpr hcenter
  have hright : center + 1 ∈ Set.Ioi (0 : ℝ) := by
    show 0 < center + 1
    linarith
  have hne : center - 1 ≠ center + 1 := by
    linarith
  have hmid := strictConcaveOn_log_Ioi.2 hleft hright hne
    (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcenterEq :
      (2 : ℝ)⁻¹ * (center - 1) + (2 : ℝ)⁻¹ * (center + 1) =
        center := by
    ring
  have hstrict :
      (2 : ℝ)⁻¹ * Real.log (center - 1) +
          (2 : ℝ)⁻¹ * Real.log (center + 1) <
        Real.log center := by
    simpa [smul_eq_mul, hcenterEq] using hmid
  unfold carryTiltThreeFirstSensitivity
  nlinarith

/-- Derivative spelling of the strict local carry sensitivity. -/
theorem deriv_cpTilt_three_zero_pos
    {center : ℝ} (hcenter : 1 < center) :
    0 < deriv (fun delta : ℝ ↦ cpTilt 3 delta center) 0 := by
  rw [(hasDerivAt_cpTilt_three_zero hcenter).deriv]
  exact carryTiltThreeFirstSensitivity_pos hcenter

/-- Real critical-carrier weighting of one canonical C3 tilt block. -/
def canonicalRealCriticalWeightedTiltBlock (k : ℕ) (delta : ℝ) : ℝ :=
  (canonicalRealCpCenter k) ^ (-(1 : ℝ) / 2) *
    cpTilt 3 delta (canonicalRealCpCenter k)

/-- Its exact first sensitivity at the centered displacement. -/
def canonicalRealCriticalWeightedTiltFirstSensitivity (k : ℕ) : ℝ :=
  (canonicalRealCpCenter k) ^ (-(1 : ℝ) / 2) *
    carryTiltThreeFirstSensitivity (canonicalRealCpCenter k)

private theorem one_lt_canonicalRealCpCenter_local (k : ℕ) :
    (1 : ℝ) < canonicalRealCpCenter k := by
  unfold canonicalRealCpCenter
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  nlinarith

theorem hasDerivAt_canonicalRealCriticalWeightedTiltBlock_zero (k : ℕ) :
    HasDerivAt (canonicalRealCriticalWeightedTiltBlock k)
      (canonicalRealCriticalWeightedTiltFirstSensitivity k) 0 := by
  unfold canonicalRealCriticalWeightedTiltBlock
    canonicalRealCriticalWeightedTiltFirstSensitivity
  exact (hasDerivAt_cpTilt_three_zero
    (one_lt_canonicalRealCpCenter_local k)).const_mul _

/-- Every canonical critical-weighted C3 cell has a strictly positive first
tilt sensitivity. -/
theorem canonicalRealCriticalWeightedTiltFirstSensitivity_pos (k : ℕ) :
    0 < canonicalRealCriticalWeightedTiltFirstSensitivity k := by
  unfold canonicalRealCriticalWeightedTiltFirstSensitivity
  exact mul_pos
    (Real.rpow_pos_of_pos
      (lt_trans zero_lt_one (one_lt_canonicalRealCpCenter_local k)) _)
    (carryTiltThreeFirstSensitivity_pos
      (one_lt_canonicalRealCpCenter_local k))

/-- Finite critical-weighted tilt ledger in the real displacement
coordinate. -/
def finiteCanonicalRealCriticalWeightedTiltTrace
    (M : ℕ) (delta : ℝ) : ℝ :=
  ∑ k ∈ Finset.range M, canonicalRealCriticalWeightedTiltBlock k delta

/-- Its first variation is the sum of the exact cell sensitivities. -/
theorem hasDerivAt_finiteCanonicalRealCriticalWeightedTiltTrace_zero
    (M : ℕ) :
    HasDerivAt (finiteCanonicalRealCriticalWeightedTiltTrace M)
      (∑ k ∈ Finset.range M,
        canonicalRealCriticalWeightedTiltFirstSensitivity k) 0 := by
  unfold finiteCanonicalRealCriticalWeightedTiltTrace
  exact HasDerivAt.fun_sum fun k _hk ↦
    hasDerivAt_canonicalRealCriticalWeightedTiltBlock_zero k

/-- Every nonempty finite geometric ledger has strictly positive centered
first variation. -/
theorem deriv_finiteCanonicalRealCriticalWeightedTiltTrace_zero_pos
    {M : ℕ} (hM : 0 < M) :
    0 < deriv (finiteCanonicalRealCriticalWeightedTiltTrace M) 0 := by
  rw [(hasDerivAt_finiteCanonicalRealCriticalWeightedTiltTrace_zero M).deriv]
  exact Finset.sum_pos' (fun k _hk ↦
    (canonicalRealCriticalWeightedTiltFirstSensitivity_pos k).le)
    ⟨0, by simpa using hM,
      canonicalRealCriticalWeightedTiltFirstSensitivity_pos 0⟩

/-! ## Identification with the existing complex product-rule channel -/

/-- On the real spectral axis, the existing phase-bearing critical tilt block
is exactly the complexification of the real weighted block above. -/
theorem canonicalCriticalWeightedTiltBlock_ofReal_displacement
    (k : ℕ) (delta : ℝ) :
    canonicalCriticalWeightedTiltBlock k
        (((1 : ℝ) / 2 + delta : ℝ) : ℂ) =
      (canonicalRealCriticalWeightedTiltBlock k delta : ℂ) := by
  have hcenter : 0 ≤ canonicalRealCpCenter k := by
    exact (lt_trans zero_lt_one
      (one_lt_canonicalRealCpCenter_local k)).le
  unfold canonicalCriticalWeightedTiltBlock
    canonicalRealCriticalWeightedTiltBlock localCriticalLineCarrier
    criticalLineDirichletCarrier
  have hdelta : criticalDisplacement ((1 : ℝ) / 2 + delta) = delta := by
    unfold criticalDisplacement
    ring
  simp only [Complex.ofReal_im, Complex.ofReal_re, Int.cast_zero,
    Complex.ofReal_zero, mul_zero, add_zero]
  rw [hdelta]
  have hexponent :
      -(1 / 2 : ℂ) = ((-(1 : ℝ) / 2 : ℝ) : ℂ) := by
    norm_num
  rw [hexponent, ← Complex.ofReal_cpow hcenter, Complex.ofReal_mul]

/-- The finite real tilt ledger is not a new normalization: it is exactly the
real-axis form of the weighted-tilt channel in the existing product rule. -/
theorem finiteCanonicalCriticalWeightedTiltTrace_ofReal_displacement
    (M : ℕ) (delta : ℝ) :
    finiteCanonicalCriticalWeightedTiltTrace M
        (((1 : ℝ) / 2 + delta : ℝ) : ℂ) =
      (finiteCanonicalRealCriticalWeightedTiltTrace M delta : ℂ) := by
  unfold finiteCanonicalCriticalWeightedTiltTrace
    finiteCanonicalRealCriticalWeightedTiltTrace
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  simpa using
    (canonicalCriticalWeightedTiltBlock_ofReal_displacement k delta)

/-- The actual critical weighted-tilt channel in the complex product-rule
ledger therefore has strictly positive real first variation at every
nonempty cutoff. -/
theorem deriv_finiteCanonicalCriticalWeightedTiltTrace_realAxis_re_zero_pos
    {M : ℕ} (hM : 0 < M) :
    0 < deriv
      (fun delta : ℝ ↦
        (finiteCanonicalCriticalWeightedTiltTrace M
          (((1 : ℝ) / 2 + delta : ℝ) : ℂ)).re) 0 := by
  rw [show (fun delta : ℝ ↦
      (finiteCanonicalCriticalWeightedTiltTrace M
        (((1 : ℝ) / 2 + delta : ℝ) : ℂ)).re) =
      finiteCanonicalRealCriticalWeightedTiltTrace M by
    funext delta
    rw [finiteCanonicalCriticalWeightedTiltTrace_ofReal_displacement]
    simp]
  exact deriv_finiteCanonicalRealCriticalWeightedTiltTrace_zero_pos hM

/-- Exact real-axis product-rule ledger.  The positive tilt channel and the
critical-carrier curvature/cross remainder remain separate. -/
theorem finiteCanonicalBracketTrace_realAxis_eq_weightedTilt_add_remainder
    (M : ℕ) (delta : ℝ) :
    (finiteCanonicalBracketTrace M
        (((1 : ℝ) / 2 + delta : ℝ) : ℂ)).re =
      finiteCanonicalRealCriticalWeightedTiltTrace M delta +
        (finiteCanonicalCriticalCarrierRemainderTrace M
          (((1 : ℝ) / 2 + delta : ℝ) : ℂ)).re := by
  have h := congrArg Complex.re
    (finiteCanonicalBracketTrace_eq_weightedTilt_add_carrierRemainder
      M (((1 : ℝ) / 2 + delta : ℝ) : ℂ))
  rw [finiteCanonicalCriticalWeightedTiltTrace_ofReal_displacement] at h
  simpa using h

/-- Real-axis form of the complete finite canonical bracket trace. -/
def finiteCanonicalBracketTraceRealAxis (M : ℕ) (delta : ℝ) : ℝ :=
  (finiteCanonicalBracketTrace M
    (((1 : ℝ) / 2 + delta : ℝ) : ℂ)).re

/-- Real-axis form of the carrier-curvature and cross-channel remainder. -/
def finiteCanonicalCriticalCarrierRemainderTraceRealAxis
    (M : ℕ) (delta : ℝ) : ℝ :=
  (finiteCanonicalCriticalCarrierRemainderTrace M
    (((1 : ℝ) / 2 + delta : ℝ) : ℂ)).re

/-- The derivative of the full finite bracket ledger is the real part of the
existing canonical log-jet trace. -/
theorem hasDerivAt_finiteCanonicalBracketTraceRealAxis_zero (M : ℕ) :
    HasDerivAt (finiteCanonicalBracketTraceRealAxis M)
      (-finiteCanonicalLogBracketChart M (1 / 2 : ℂ)).re 0 := by
  have hcomplex : HasDerivAt (finiteCanonicalBracketTrace M)
      (-finiteCanonicalLogBracketChart M (1 / 2 : ℂ)) (1 / 2 : ℂ) := by
    unfold finiteCanonicalBracketTrace finiteCanonicalLogBracketChart
    have hsum : HasDerivAt
        (fun s : ℂ ↦ ∑ k ∈ Finset.range M,
          realCpSaturatedBracket 3 k s)
        (∑ k ∈ Finset.range M,
          -canonicalLogBracketBlock k (1 / 2 : ℂ)) (1 / 2 : ℂ) := by
      exact HasDerivAt.fun_sum fun k _hk ↦
        hasDerivAt_realCpSaturatedBracket_three_eq_neg_logBracket
          k (1 / 2 : ℂ)
    simpa [Finset.sum_neg_distrib] using hsum
  have hcomplex' : HasDerivAt (finiteCanonicalBracketTrace M)
      (-finiteCanonicalLogBracketChart M (1 / 2 : ℂ))
        (((1 : ℝ) / 2 : ℝ) : ℂ) := by
    simpa using hcomplex
  have hreal := hcomplex'.real_of_complex
  have hshift : HasDerivAt (fun delta : ℝ ↦ (1 : ℝ) / 2 + delta) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add ((1 : ℝ) / 2)
  have hrealAtShift : HasDerivAt
      (fun x : ℝ ↦ (finiteCanonicalBracketTrace M (x : ℂ)).re)
      (-finiteCanonicalLogBracketChart M (1 / 2 : ℂ)).re
      ((fun delta : ℝ ↦ (1 : ℝ) / 2 + delta) 0) := by
    simpa using hreal
  have hcomp := hrealAtShift.comp 0 hshift
  unfold finiteCanonicalBracketTraceRealAxis
  simpa [Function.comp_def, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hcomp

/-- The complete product-rule remainder is differentiable at the center, and
its first variation is exactly what remains after subtracting the positive
weighted-tilt sensitivity from the full logarithmic bracket variation. -/
theorem
    hasDerivAt_finiteCanonicalCriticalCarrierRemainderTraceRealAxis_zero
    (M : ℕ) :
    HasDerivAt (finiteCanonicalCriticalCarrierRemainderTraceRealAxis M)
      ((-finiteCanonicalLogBracketChart M (1 / 2 : ℂ)).re -
        ∑ k ∈ Finset.range M,
          canonicalRealCriticalWeightedTiltFirstSensitivity k) 0 := by
  have hfull := hasDerivAt_finiteCanonicalBracketTraceRealAxis_zero M
  have htilt :=
    hasDerivAt_finiteCanonicalRealCriticalWeightedTiltTrace_zero M
  have hdiff := hfull.sub htilt
  rw [show finiteCanonicalCriticalCarrierRemainderTraceRealAxis M =
      fun delta : ℝ ↦
        finiteCanonicalBracketTraceRealAxis M delta -
          finiteCanonicalRealCriticalWeightedTiltTrace M delta by
    funext delta
    have hledger :=
      finiteCanonicalBracketTrace_realAxis_eq_weightedTilt_add_remainder
        M delta
    unfold finiteCanonicalBracketTraceRealAxis
      finiteCanonicalCriticalCarrierRemainderTraceRealAxis
    linarith]
  exact hdiff

/-- Exact first-variation ledger: the full logarithmic bracket variation is
the strictly positive tilt contribution plus the carrier/cross remainder.
This is an equality, not a cancellation assumption. -/
theorem deriv_finiteCanonicalBracketTraceRealAxis_zero_eq_tilt_add_remainder
    (M : ℕ) :
    deriv (finiteCanonicalBracketTraceRealAxis M) 0 =
      (∑ k ∈ Finset.range M,
        canonicalRealCriticalWeightedTiltFirstSensitivity k) +
      deriv (finiteCanonicalCriticalCarrierRemainderTraceRealAxis M) 0 := by
  rw [(hasDerivAt_finiteCanonicalBracketTraceRealAxis_zero M).deriv,
    (hasDerivAt_finiteCanonicalCriticalCarrierRemainderTraceRealAxis_zero
      M).deriv]
  ring

/-! ## Cutoff passage without channel collapse -/

/-- Finite first-sensitivity ledger of the positive carry-tilt channel. -/
def finiteCanonicalRealCriticalWeightedTiltFirstSensitivity
    (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M,
    canonicalRealCriticalWeightedTiltFirstSensitivity k

/-- The positive channel is monotone under cutoff refinement. -/
theorem monotone_finiteCanonicalRealCriticalWeightedTiltFirstSensitivity :
    Monotone finiteCanonicalRealCriticalWeightedTiltFirstSensitivity := by
  intro M N hMN
  unfold finiteCanonicalRealCriticalWeightedTiltFirstSensitivity
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hMN)
    (fun k _hk _hkM ↦
      (canonicalRealCriticalWeightedTiltFirstSensitivity_pos k).le)

/-- Every nonempty cutoff retains at least the strictly positive first C3
cell.  Thus no cancellation occurs inside the weighted-tilt channel. -/
theorem finiteCanonicalRealCriticalWeightedTiltFirstSensitivity_pos
    {M : ℕ} (hM : 0 < M) :
    0 < finiteCanonicalRealCriticalWeightedTiltFirstSensitivity M := by
  unfold finiteCanonicalRealCriticalWeightedTiltFirstSensitivity
  exact Finset.sum_pos' (fun k _hk ↦
    (canonicalRealCriticalWeightedTiltFirstSensitivity_pos k).le)
    ⟨0, by simpa using hM,
      canonicalRealCriticalWeightedTiltFirstSensitivity_pos 0⟩

/-- A quantitative bound for the centered logarithmic curvature.  It is
strong enough to dominate the global sensitivity by a shifted `p`-series. -/
theorem carryTiltThreeFirstSensitivity_le_two_div_sq
    {center : ℝ} (hcenter : 2 ≤ center) :
    carryTiltThreeFirstSensitivity center ≤ 2 / center ^ 2 := by
  have hc : 0 < center := lt_of_lt_of_le (by norm_num) hcenter
  have hcm : 0 < center - 1 := by linarith
  have hcp : 0 < center + 1 := by linarith
  have hden : 0 < center ^ 2 - 1 := by nlinarith
  have hratio : 0 < center ^ 2 / (center ^ 2 - 1) :=
    div_pos (sq_pos_of_pos hc) hden
  have hlog :
      carryTiltThreeFirstSensitivity center =
        Real.log (center ^ 2 / (center ^ 2 - 1)) := by
    unfold carryTiltThreeFirstSensitivity
    rw [Real.log_div (sq_pos_of_pos hc).ne' hden.ne',
      show Real.log (center ^ 2) = 2 * Real.log center by
        rw [pow_two, Real.log_mul hc.ne' hc.ne']
        ring,
      show Real.log (center ^ 2 - 1) =
          Real.log (center - 1) + Real.log (center + 1) by
        rw [show center ^ 2 - 1 = (center - 1) * (center + 1) by ring,
          Real.log_mul hcm.ne' hcp.ne']]
    ring
  rw [hlog]
  calc
    Real.log (center ^ 2 / (center ^ 2 - 1)) ≤
        center ^ 2 / (center ^ 2 - 1) - 1 :=
      Real.log_le_sub_one_of_pos hratio
    _ = 1 / (center ^ 2 - 1) := by
      field_simp [hden.ne']
      ring
    _ ≤ 2 / center ^ 2 := by
      apply (div_le_div_iff₀ hden (sq_pos_of_pos hc)).2
      nlinarith [sq_nonneg center]

/-- Each weighted cell sensitivity is bounded by a shifted square
`p`-series term. -/
theorem canonicalRealCriticalWeightedTiltFirstSensitivity_le_pseries
    (k : ℕ) :
    canonicalRealCriticalWeightedTiltFirstSensitivity k ≤
      2 * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
  let center := canonicalRealCpCenter k
  let index : ℝ := ((k + 1 : ℕ) : ℝ)
  have hindex : 0 < index := by
    dsimp [index]
    positivity
  have hcenter : center = 3 * index := by
    simp [center, index, canonicalRealCpCenter]
  have hcenterTwo : 2 ≤ center := by
    rw [hcenter]
    have : 1 ≤ index := by
      dsimp [index]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith
  have hcenterPos : 0 < center := lt_of_lt_of_le (by norm_num) hcenterTwo
  have hweightNonneg : 0 ≤ center ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg hcenterPos.le _
  have hweightLe : center ^ (-(1 : ℝ) / 2) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (le_trans (by norm_num) hcenterTwo) (by norm_num)
  have hsensitivityNonneg :
      0 ≤ carryTiltThreeFirstSensitivity center :=
    (carryTiltThreeFirstSensitivity_pos
      (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hcenterTwo)).le
  have hcenterBound :=
    carryTiltThreeFirstSensitivity_le_two_div_sq hcenterTwo
  have hdenCompare : 2 / center ^ 2 ≤ 2 / index ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hcenterPos)
      (sq_pos_of_pos hindex)).2
    rw [hcenter]
    nlinarith [sq_nonneg index]
  unfold canonicalRealCriticalWeightedTiltFirstSensitivity
  change center ^ (-(1 : ℝ) / 2) *
      carryTiltThreeFirstSensitivity center ≤ _
  calc
    center ^ (-(1 : ℝ) / 2) *
          carryTiltThreeFirstSensitivity center ≤
        1 * carryTiltThreeFirstSensitivity center :=
      mul_le_mul_of_nonneg_right hweightLe hsensitivityNonneg
    _ ≤ 2 / center ^ 2 := by simpa using hcenterBound
    _ ≤ 2 / index ^ 2 := hdenCompare
    _ = 2 * index ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hindex.le, Real.rpow_two]
      simp [div_eq_mul_inv]

/-- The complete weighted-tilt first-sensitivity family is absolutely
summable.  Consequently its positive finite ledgers have a genuine global
limit rather than merely an increasing extended-real supremum. -/
theorem summable_canonicalRealCriticalWeightedTiltFirstSensitivity :
    Summable canonicalRealCriticalWeightedTiltFirstSensitivity := by
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := hbase.comp_injective
    (show Function.Injective (fun n : ℕ ↦ n + 1) by
      intro a b hab
      exact Nat.add_right_cancel hab)
  have hmajorant : Summable
      (fun k : ℕ ↦ 2 * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
    simpa [Function.comp_def] using hshift.mul_left 2
  exact hmajorant.of_nonneg_of_le
    (fun k ↦ (canonicalRealCriticalWeightedTiltFirstSensitivity_pos k).le)
    canonicalRealCriticalWeightedTiltFirstSensitivity_le_pseries

/-- Global positive carry-tilt sensitivity before the carrier/cross and
completion channels are assembled. -/
def canonicalRealCriticalWeightedTiltTotalSensitivity : ℝ :=
  ∑' k : ℕ, canonicalRealCriticalWeightedTiltFirstSensitivity k

/-- The global geometric tilt sensitivity is strictly positive. -/
theorem canonicalRealCriticalWeightedTiltTotalSensitivity_pos :
    0 < canonicalRealCriticalWeightedTiltTotalSensitivity := by
  unfold canonicalRealCriticalWeightedTiltTotalSensitivity
  exact summable_canonicalRealCriticalWeightedTiltFirstSensitivity.tsum_pos
    (fun k ↦ (canonicalRealCriticalWeightedTiltFirstSensitivity_pos k).le)
    0 (canonicalRealCriticalWeightedTiltFirstSensitivity_pos 0)

/-- Finite positive tilt ledgers converge to their strictly positive global
geometric sensitivity. -/
theorem finiteCanonicalRealCriticalWeightedTiltFirstSensitivity_tendsto_total :
    Filter.Tendsto finiteCanonicalRealCriticalWeightedTiltFirstSensitivity
      Filter.atTop
      (nhds canonicalRealCriticalWeightedTiltTotalSensitivity) := by
  unfold finiteCanonicalRealCriticalWeightedTiltFirstSensitivity
    canonicalRealCriticalWeightedTiltTotalSensitivity
  exact
    summable_canonicalRealCriticalWeightedTiltFirstSensitivity.hasSum.tendsto_sum_nat

/-- The derivative of the full native bracket ledger converges to the exact
completed TFVD log-jet readout.  This passes the complete native channel to
the limit, before the archimedean completion factor is applied. -/
theorem deriv_finiteCanonicalBracketTraceRealAxis_zero_tendsto_completedLogJet :
    Filter.Tendsto
      (fun M : ℕ ↦ deriv (finiteCanonicalBracketTraceRealAxis M) 0)
      Filter.atTop
      (nhds
        (-canonicalCompletedC3EnrichedTfvdLogJetTailReadout
          (1 / 2 : ℂ)).re) := by
  have hhead := finiteCanonicalLogBracketChart_tendsto_completed
    (s := (1 / 2 : ℂ)) (by norm_num)
  have hlimit :=
    Complex.continuous_re.continuousAt.tendsto.comp hhead.neg
  refine hlimit.congr' (Filter.Eventually.of_forall fun M ↦ ?_)
  change (-finiteCanonicalLogBracketChart M (1 / 2 : ℂ)).re =
    deriv (finiteCanonicalBracketTraceRealAxis M) 0
  rw [(hasDerivAt_finiteCanonicalBracketTraceRealAxis_zero M).deriv]

/-- The global carrier-curvature/cross sensitivity is the exact complement
of the positive tilt channel inside the completed native log-jet. -/
def canonicalRealCriticalCarrierRemainderTotalSensitivity : ℝ :=
  (-canonicalCompletedC3EnrichedTfvdLogJetTailReadout
      (1 / 2 : ℂ)).re -
    canonicalRealCriticalWeightedTiltTotalSensitivity

/-- The finite carrier/cross remainders converge to their exact global
complement.  This is the all-cutoff passage of the product-rule ledger; no
remainder has been assumed to vanish. -/
theorem
    deriv_finiteCanonicalCriticalCarrierRemainderTraceRealAxis_zero_tendsto_total :
    Filter.Tendsto
      (fun M : ℕ ↦
        deriv (finiteCanonicalCriticalCarrierRemainderTraceRealAxis M) 0)
      Filter.atTop
      (nhds canonicalRealCriticalCarrierRemainderTotalSensitivity) := by
  have hsub :=
    deriv_finiteCanonicalBracketTraceRealAxis_zero_tendsto_completedLogJet.sub
      finiteCanonicalRealCriticalWeightedTiltFirstSensitivity_tendsto_total
  unfold canonicalRealCriticalCarrierRemainderTotalSensitivity
  refine hsub.congr' (Filter.Eventually.of_forall fun M ↦ ?_)
  change
    deriv (finiteCanonicalBracketTraceRealAxis M) 0 -
        finiteCanonicalRealCriticalWeightedTiltFirstSensitivity M =
      deriv (finiteCanonicalCriticalCarrierRemainderTraceRealAxis M) 0
  rw [deriv_finiteCanonicalBracketTraceRealAxis_zero_eq_tilt_add_remainder]
  unfold finiteCanonicalRealCriticalWeightedTiltFirstSensitivity
  ring

/-- Exact infinite first-variation ledger.  The native completed TFVD
log-jet consists of the strictly positive geometric tilt total plus the
explicit carrier/cross total. -/
theorem completedNativeLogJetRealFirstVariation_eq_tilt_add_remainder :
    (-canonicalCompletedC3EnrichedTfvdLogJetTailReadout
        (1 / 2 : ℂ)).re =
      canonicalRealCriticalWeightedTiltTotalSensitivity +
        canonicalRealCriticalCarrierRemainderTotalSensitivity := by
  unfold canonicalRealCriticalCarrierRemainderTotalSensitivity
  ring

end

end CarrySelfAdjointOperator

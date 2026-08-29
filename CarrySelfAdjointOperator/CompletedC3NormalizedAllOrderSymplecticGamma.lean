import CarrySelfAdjointOperator.CompletedC3AllOrderGammaWronskianLimitGate
import Mathlib.Tactic

/-!
# Normalized all-order symplectic Gamma gate

The real/complex bridge identifies the symplectic Gamma packing as the
Green-compatible carrier for the completed all-camera source.  This file
normalizes that carrier by the raw completed C3 value trace, without changing
coordinates or discarding a channel.

The resulting kernel is a genuine Gram kernel and hence positive
semidefinite.  Away from zeros of the raw value and from the Cauchy diagonal,
its equality with the normalized raw Wronskian is proved equivalent to the
already explicit three-channel cutoff defect tending to zero.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace
  RealInnerProductSpace Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-! ## Canonical raw-trace normalization -/

/-- Hermitian weight determined by the raw completed C3 value trace. -/
def canonicalCompletedC3RawHeightCharacteristicWeight (z w : ℂ) : ℂ :=
  (2 : ℂ) * conj (canonicalCompletedC3RawHeightValue z) *
    canonicalCompletedC3RawHeightValue w

/-- The all-order symplectic Gamma state with the exact raw C3 normalization.
The total inverse keeps the definition meaningful at zeros; cancellation is
used only in the off-zero sewing theorem below. -/
def canonicalCompletedC3NormalizedAllOrderSymplecticGammaState
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    CarryGammaComplexNaimark :=
  ((((Real.sqrt 2 : ℝ) : ℂ) *
      canonicalCompletedC3RawHeightValue z)⁻¹) •
    canonicalCompletedC3AllOrderSymplecticGammaState z hz hzStrip

/-- The all-order positive Gamma kernel divided by the same raw C3 weight
which normalizes the raw Wronskian. -/
def canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) : ℂ :=
  canonicalCompletedC3AllOrderSymplecticGammaKernel
      z w hz hw hzStrip hwStrip /
    canonicalCompletedC3RawHeightCharacteristicWeight z w

/-- The normalized all-order kernel is exactly the Gram kernel of the
normalized symplectic Gamma responses. -/
theorem canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel_eq_inner
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel
        z w hz hw hzStrip hwStrip =
      inner ℂ
        (canonicalCompletedC3NormalizedAllOrderSymplecticGammaState
          z hz hzStrip)
        (canonicalCompletedC3NormalizedAllOrderSymplecticGammaState
          w hw hwStrip) := by
  unfold canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel
    canonicalCompletedC3RawHeightCharacteristicWeight
    canonicalCompletedC3NormalizedAllOrderSymplecticGammaState
    canonicalCompletedC3AllOrderSymplecticGammaKernel
  have hsqrt_sq : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hsqrt_inv_sq : (2 : ℂ)⁻¹ =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [← hsqrt_sq, ← inv_pow, pow_two]
  rw [inner_smul_left, inner_smul_right]
  simp only [map_inv₀, map_mul, Complex.conj_ofReal]
  simp only [div_eq_mul_inv, mul_inv]
  rw [hsqrt_inv_sq]
  ring

/-- Every finite section of the normalized all-order symplectic Gamma kernel
is positive semidefinite, independently of the pending sewing. -/
theorem canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hoffAxis : ∀ i, (point i).im ≠ 0)
    (hstrip : ∀ i, operatorHeightParameter (point i) ∈
      genuineCriticalStrip) :
    (Matrix.of fun i j ↦
      canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel
        (point i) (point j) (hoffAxis i) (hoffAxis j)
        (hstrip i) (hstrip j)).PosSemidef := by
  rw [show (Matrix.of fun i j ↦
      canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel
        (point i) (point j) (hoffAxis i) (hoffAxis j)
        (hstrip i) (hstrip j)) =
      Matrix.gram ℂ (fun i ↦
        canonicalCompletedC3NormalizedAllOrderSymplecticGammaState
          (point i) (hoffAxis i) (hstrip i)) by
    ext i j
    exact
      canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel_eq_inner
        (point i) (point j) (hoffAxis i) (hoffAxis j)
        (hstrip i) (hstrip j)]
  exact Matrix.posSemidef_gram ℂ _

/-! ## Exact normalized Wronskian gate -/

/-- Raw completed C3 Wronskian divided by its exact characteristic and
Cauchy-separation factors, in the orientation used by the all-order Gamma
boundary. -/
def canonicalCompletedC3NormalizedRawHeightWronskianKernel
    (z w : ℂ) : ℂ :=
  canonicalCompletedC3RawHeightMixedWronskian w z /
    (canonicalCompletedC3RawHeightCharacteristicWeight z w *
      (w - conj z))

/-- Off zeros and off the Cauchy diagonal, equality of the two normalized
kernels is exactly the division-free Gamma--Wronskian sewing. -/
theorem canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel_eq_rawWronskianKernel_iff
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzRaw : canonicalCompletedC3RawHeightValue z ≠ 0)
    (hwRaw : canonicalCompletedC3RawHeightValue w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel
        z w hz hw hzStrip hwStrip =
        canonicalCompletedC3NormalizedRawHeightWronskianKernel z w ↔
      canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
          z w hz hw hzStrip hwStrip =
        canonicalCompletedC3RawHeightMixedWronskian w z := by
  have hzRawStar : conj (canonicalCompletedC3RawHeightValue z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzRaw
  have hweight :
      canonicalCompletedC3RawHeightCharacteristicWeight z w ≠ 0 := by
    unfold canonicalCompletedC3RawHeightCharacteristicWeight
    exact mul_ne_zero (mul_ne_zero (by norm_num) hzRawStar) hwRaw
  have hseparation : w - conj z ≠ 0 := sub_ne_zero.mpr hsep
  rw [canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout_eq_kernel]
  unfold canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel
    canonicalCompletedC3NormalizedRawHeightWronskianKernel
  constructor
  · intro h
    field_simp [hweight, hseparation] at h ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  · intro h
    field_simp [hweight, hseparation] at h ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Concrete form of the next gate: normalized Gram equals normalized raw
Wronskian exactly when the already exposed dynamic/static, structural, and
head--tail cutoff channels tend to zero. -/
theorem canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel_eq_rawWronskianKernel_iff_tendsto
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzRaw : canonicalCompletedC3RawHeightValue z ≠ 0)
    (hwRaw : canonicalCompletedC3RawHeightValue w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel
        z w hz hw hzStrip hwStrip =
        canonicalCompletedC3NormalizedRawHeightWronskianKernel z w ↔
      Tendsto
        (fun M : ℕ ↦
          canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference
            M z w hz hw)
        atTop (nhds 0) := by
  rw [canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel_eq_rawWronskianKernel_iff
      z w hz hw hzStrip hwStrip hzRaw hwRaw hsep,
    canonicalCompletedC3AllOrderSymplecticGammaBoundary_eq_rawWronskian_iff_tendsto
      z w hz hw hzStrip hwStrip]

/-- State-level form of the same gate.  It exposes the Hilbert inner product
directly and leaves the finite three-channel expression as the sole remaining
limit statement. -/
theorem inner_canonicalCompletedC3NormalizedAllOrderSymplecticGammaState_eq_rawWronskianKernel_iff_tendsto
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzRaw : canonicalCompletedC3RawHeightValue z ≠ 0)
    (hwRaw : canonicalCompletedC3RawHeightValue w ≠ 0)
    (hsep : w ≠ conj z) :
    inner ℂ
        (canonicalCompletedC3NormalizedAllOrderSymplecticGammaState
          z hz hzStrip)
        (canonicalCompletedC3NormalizedAllOrderSymplecticGammaState
          w hw hwStrip) =
        canonicalCompletedC3NormalizedRawHeightWronskianKernel z w ↔
      Tendsto
        (fun M : ℕ ↦
          canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference
            M z w hz hw)
        atTop (nhds 0) := by
  rw [← canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel_eq_inner,
    canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel_eq_rawWronskianKernel_iff_tendsto
      z w hz hw hzStrip hwStrip hzRaw hwRaw hsep]

/-! ## Audit at a hypothetical off-critical zero -/

/-- At a hypothetical Genuine zero away from the critical line, the completed
dynamic-to-static Gamma limit cannot equal the completed structural limit.
Indeed, their equality would identify the nonzero diagonal Gamma boundary with
the zero raw Wronskian. -/
theorem canonicalCompletedC3AllOrderSymplecticGammaDynamicStaticDifference_ne_structural_at_offCriticalGenuineZero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) (hoff : s.re ≠ 1 / 2) :
    canonicalCompletedC3AllOrderSymplecticGammaDynamicStaticDifference
        (centeredHeightParameter s) (centeredHeightParameter s)
        (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)
        (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)
        (by simpa using hs) (by simpa using hs) ≠
      canonicalCompletedC3AllOrderStructuralChannelLimit
        (centeredHeightParameter s) (centeredHeightParameter s)
        (by simpa using hs) (by simpa using hs) := by
  let z := centeredHeightParameter s
  have hz : z.im ≠ 0 :=
    centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
  have hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip := by
    simpa [z] using hs
  have hboundaryNe :
      canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
          z z hz hz hzStrip hzStrip ≠ 0 :=
    canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout_diagonal_ne_zero
      hz hzStrip
  have hwronskian :
      canonicalCompletedC3RawHeightMixedWronskian z z = 0 := by
    simpa [z] using
      canonicalCompletedC3RawHeightMixedWronskian_self_eq_zero_of_genuine_zero
        hs hzero
  intro hchannels
  have hboundary :
      canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
          z z hz hz hzStrip hzStrip =
        canonicalCompletedC3RawHeightMixedWronskian z z := by
    have hadd := congrArg
      (fun value : ℂ => value +
        canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
          z z hzStrip hzStrip) hchannels
    simpa [canonicalCompletedC3AllOrderSymplecticGammaDynamicStaticDifference,
      canonicalCompletedC3AllOrderStructuralChannelLimit, z] using hadd
  exact hboundaryNe (hboundary.trans hwronskian)

/-- Consequently the explicit finite dynamic/static, structural, and
head--tail mismatch cannot tend to zero at a hypothetical off-critical Genuine
zero.  Thus this limit statement has confinement strength and is not supplied
by completion or by the real/complex coordinate equivalence. -/
theorem canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference_not_tendsto_zero_of_offCriticalGenuineZero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) (hoff : s.re ≠ 1 / 2) :
    ¬Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3AllCutoffSymplecticGammaWronskianChannelDifference
          M (centeredHeightParameter s) (centeredHeightParameter s)
          (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)
          (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff))
      atTop (nhds 0) := by
  let z := centeredHeightParameter s
  have hz : z.im ≠ 0 :=
    centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
  have hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip := by
    simpa [z] using hs
  have hboundaryNe :
      canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout
          z z hz hz hzStrip hzStrip ≠ 0 :=
    canonicalCompletedC3AllOrderSymplecticGammaBoundaryReadout_diagonal_ne_zero
      hz hzStrip
  have hwronskian :
      canonicalCompletedC3RawHeightMixedWronskian z z = 0 := by
    simpa [z] using
      canonicalCompletedC3RawHeightMixedWronskian_self_eq_zero_of_genuine_zero
        hs hzero
  intro hlimit
  have hboundary :=
    (canonicalCompletedC3AllOrderSymplecticGammaBoundary_eq_rawWronskian_iff_tendsto
      z z hz hz hzStrip hzStrip).2 hlimit
  exact hboundaryNe (hboundary.trans hwronskian)

end

end CarrySelfAdjointOperator

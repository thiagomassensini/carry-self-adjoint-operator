import CarrySelfAdjointOperator.CompletedNativeChiralReturnEulerBoundary
import CarrySelfAdjointOperator.CompletedNativeXiThetaMomentBounds
import Mathlib.Algebra.Ring.GeomSum

/-!
# Complete polarized Green boundary tower on the native Cauchy features

Repeated degree transport retains every ordered boundary jet pairing. The
cubic source scale comes from raw characteristic derivatives and the upstream
theta-kernel inequality. Higher source terms remain an exact vector remainder;
no Taylor polynomial replaces the completed source.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- Powers of the native monomial degree action, in the original Cauchy carrier. -/
def radialEulerPowerSynthesis (k N m : ℕ) (d : Fin N → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis k N (fun i => d i * ((i + 1 : ℕ) : ℂ) ^ m)

/-- Endpoint jet of the SAME fully synthesized polynomial coefficients. -/
def radialEulerBoundaryJet {N : ℕ} (d : Fin N → ℂ) (m : ℕ) : ℂ :=
  ∑ i, d i * ((i + 1 : ℕ) : ℂ) ^ m

@[simp] theorem radialEulerPowerSynthesis_zero (k N : ℕ) (d : Fin N → ℂ) :
    radialEulerPowerSynthesis k N 0 d = radialIncidentSynthesis k N d := by
  simp [radialEulerPowerSynthesis]

@[simp] theorem radialEulerBoundaryJet_zero {N : ℕ} (d : Fin N → ℂ) :
    radialEulerBoundaryJet d 0 = ∑ i, d i := by simp [radialEulerBoundaryJet]

/-- Pairing of arbitrary degree powers, retaining both coefficient families. -/
theorem radialEulerPower_inner (k N a b : ℕ) (d e : Fin N → ℂ) :
    inner ℂ (radialEulerPowerSynthesis k N a d) (radialEulerPowerSynthesis k N b e) =
      ∑ i, ∑ j, conj (d i) * e j * ((i + 1 : ℕ) : ℂ) ^ a *
        ((j + 1 : ℕ) : ℂ) ^ b *
          ((((k : ℝ) + 1 : ℝ) : ℂ) / (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℂ)) := by
  classical
  simp only [radialEulerPowerSynthesis, radialIncidentSynthesis,
    LinearMap.coe_mk, AddHom.coe_mk, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, map_mul, map_pow, map_natCast,
    inner_completedNativeRadialChiralCauchyState, Complex.ofReal_mul, Complex.ofReal_inv,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

private theorem degree_green_polynomial (x y : ℂ) (m : ℕ) :
    y ^ m - (-1 : ℂ) ^ m * x ^ m =
      (x + y) * ∑ a ∈ Finset.range m, (-1 : ℂ) ^ a * x ^ a * y ^ (m - 1 - a) := by
  have h := geom_sum₂_mul (-x) y m
  have hp (a : ℕ) : (-x) ^ a = (-1 : ℂ) ^ a * x ^ a := by
    rw [neg_eq_neg_one_mul, mul_pow]
  simp only [hp] at h
  linear_combination h

/-- All-order discrete Green identity. It is a boundary form with alternating
ordered crosses, not a positive squared-norm statement. -/
theorem radialEulerPower_green_boundary (k N m : ℕ) (d e : Fin N → ℂ) :
    inner ℂ (radialEulerPowerSynthesis k N 0 d) (radialEulerPowerSynthesis k N m e) -
      (-1 : ℂ) ^ m *
        inner ℂ (radialEulerPowerSynthesis k N m d) (radialEulerPowerSynthesis k N 0 e) =
      (((k : ℝ) + 1 : ℝ) : ℂ) * ∑ a ∈ Finset.range m,
        (-1 : ℂ) ^ a * conj (radialEulerBoundaryJet d a) *
          radialEulerBoundaryJet e (m - 1 - a) := by
  classical
  simp only [radialEulerPower_inner, pow_zero, mul_one, Finset.mul_sum,
    radialEulerBoundaryJet, map_sum, map_mul, map_pow, map_natCast, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := Finset.range m)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (s := Finset.range m)]
  apply Finset.sum_congr rfl
  intro j _
  have h : (((j + 1 : ℕ) : ℂ) + ((i + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show (j : ℕ) + 1 + ((i : ℕ) + 1) ≠ 0 by omega)
  have hp := degree_green_polynomial ((j + 1 : ℕ) : ℂ) ((i + 1 : ℕ) : ℂ) m
  rw [show (((j : ℕ) + (i : ℕ) + 2 : ℕ) : ℂ) =
      ((j + 1 : ℕ) : ℂ) + ((i + 1 : ℕ) : ℂ) by push_cast; ring]
  have hs : (∑ a ∈ Finset.range m, (((k : ℝ) + 1 : ℝ) : ℂ) *
        ((-1 : ℂ) ^ a * (conj (d j) * ((j + 1 : ℕ) : ℂ) ^ a) *
          (e i * ((i + 1 : ℕ) : ℂ) ^ (m - 1 - a)))) =
      (conj (d j) * e i * (((k : ℝ) + 1 : ℝ) : ℂ)) *
        ∑ a ∈ Finset.range m, (-1 : ℂ) ^ a * ((j + 1 : ℕ) : ℂ) ^ a *
          ((i + 1 : ℕ) : ℂ) ^ (m - 1 - a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hs]
  field_simp [h]
  linear_combination conj (d j) * e i * hp

/-- Cubic Green identity with both ordered value/curvature crosses retained. -/
theorem radialEuler_cubic_boundary_polarized (k N : ℕ) (d e : Fin N → ℂ) :
    inner ℂ (radialIncidentSynthesis k N d) (radialEulerPowerSynthesis k N 3 e) +
      inner ℂ (radialEulerPowerSynthesis k N 3 d) (radialIncidentSynthesis k N e) =
      (((k : ℝ) + 1 : ℝ) : ℂ) *
        (conj (radialEulerBoundaryJet d 0) * radialEulerBoundaryJet e 2 -
          conj (radialEulerBoundaryJet d 1) * radialEulerBoundaryJet e 1 +
          conj (radialEulerBoundaryJet d 2) * radialEulerBoundaryJet e 0) := by
  have h := radialEulerPower_green_boundary k N 3 d e
  norm_num [Finset.sum_range_succ] at h
  simpa [radialEulerBoundaryJet_zero, Complex.ofReal_add, sub_eq_add_neg] using h

/-- Diagonal cubic boundary energy: the value/curvature cross must not be
silently deleted. On a zero value trace only the signed slope energy remains. -/
theorem radialEuler_cubic_boundary_energy (k N : ℕ) (d : Fin N → ℂ) :
    (inner ℂ (radialIncidentSynthesis k N d) (radialEulerPowerSynthesis k N 3 d)).re =
      ((k : ℝ) + 1) *
        ((conj (radialEulerBoundaryJet d 0) * radialEulerBoundaryJet d 2).re -
          Complex.normSq (radialEulerBoundaryJet d 1) / 2) := by
  have h := congrArg Complex.re (radialEuler_cubic_boundary_polarized k N d d)
  have hi := congrArg Complex.re (inner_conj_symm
    (radialIncidentSynthesis k N d) (radialEulerPowerSynthesis k N 3 d))
  rw [← Complex.normSq_eq_conj_mul_self] at h
  simp only [Complex.conj_re] at hi
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero] at h ⊢
  nlinarith

/-- Raw cubic source scale, fixed by F(0), F''(0), F''''(0) and the radial grid.
This definition uses neither canonical logarithmic moments nor a target metric. -/
def radialCompletedCubicScale (k : ℕ) : ℝ :=
  ((iteratedDeriv 4 completedNativeOperatorCharacteristic 0 *
      completedNativeOperatorCharacteristic 0 -
        3 * (iteratedDeriv 2 completedNativeOperatorCharacteristic 0) ^ 2) /
    (6 * completedNativeOperatorCharacteristic 0 ^ 2)).re / ((k : ℝ) + 1) ^ 3

/-- The cubic scale is exactly the upstream source-integral discriminant. -/
theorem radialCompletedCubicScale_eq_sourceIntegrals (k : ℕ) :
    radialCompletedCubicScale k =
      (completedNativeXiCosineMoment 2 * completedNativeXiCosineMoment 0 -
        3 * completedNativeXiCosineMoment 1 ^ 2) /
          (6 * completedNativeXiCosineMoment 0 ^ 2) / ((k : ℝ) + 1) ^ 3 := by
  have h0 : completedNativeOperatorCharacteristic 0 = (completedNativeXiCosineMoment 0 : ℂ) := by
    have ha : completedNativeOperatorCharacteristic 0 =
        (completedNativeXiCosineTransformReal 0 : ℂ) := by
      simpa [completedNativeXiCosineTransformReal] using
        XiThetaCosine.completedNative_eq_xiCosineKernel 0
    rw [ha, completedNativeXiCosineTransformReal_zero]
  unfold radialCompletedCubicScale
  rw [iteratedDeriv_two_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_four_completedNativeOperatorCharacteristic_zero, h0]
  norm_cast
  simp only [neg_sq]

/-- The existing strict theta-kernel fourth-integral inequality gives the
actual negative cubic scale, independently of a moment-positivity certificate. -/
theorem radialCompletedCubicScale_neg (k : ℕ) : radialCompletedCubicScale k < 0 := by
  rw [radialCompletedCubicScale_eq_sourceIntegrals]
  have hn : completedNativeXiCosineMoment 2 * completedNativeXiCosineMoment 0 -
      3 * completedNativeXiCosineMoment 1 ^ 2 < 0 := by
    nlinarith [completedNativeXiCosineMoment_strict_kurtosis]
  exact div_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos hn (mul_pos (by norm_num)
      (sq_pos_of_pos (completedNativeXiCosineMoment_pos 0)))) (by positivity)

/-- All remaining source orders are retained exactly, after the source's
own cubic scale is separated. No truncated response replaces the source. -/
def radialCompletedCubicRemainder (k n : ℕ) : ℂ :=
  radialCompletedEulerRemainder k n -
    (radialCompletedCubicScale k : ℂ) * ((n + 1 : ℕ) : ℂ) ^ 3

/-- Full vector synthesis of the exact higher source correction. -/
def radialCompletedCubicRemainderSynthesis (k N : ℕ) (d : Fin N → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis k N (fun i => d i * radialCompletedCubicRemainder k i)

/-- The previous exact source remainder splits vectorially; both parts remain. -/
theorem radialCompletedRemainder_eq_cubic_add_higher (k N : ℕ) (d : Fin N → ℂ) :
    radialCompletedRemainderSynthesis k N d =
      (radialCompletedCubicScale k : ℂ) • radialEulerPowerSynthesis k N 3 d +
        radialCompletedCubicRemainderSynthesis k N d := by
  simp only [radialCompletedRemainderSynthesis, radialCompletedCubicRemainderSynthesis,
    radialEulerPowerSynthesis, radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, ← add_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold radialCompletedCubicRemainder
  ring

/-- Exact correction pairing: value/curvature cross, slope energy, and the
higher completed vector correction. None of these terms is discarded. -/
theorem radialCompletedRemainder_pairing_eq_green_boundary (k N : ℕ) (d : Fin N → ℂ) :
    (inner ℂ (radialIncidentSynthesis k N d) (radialCompletedRemainderSynthesis k N d)).re =
      radialCompletedCubicScale k * ((k : ℝ) + 1) *
        ((conj (radialEulerBoundaryJet d 0) * radialEulerBoundaryJet d 2).re -
          Complex.normSq (radialEulerBoundaryJet d 1) / 2) +
      (inner ℂ (radialIncidentSynthesis k N d) (radialCompletedCubicRemainderSynthesis k N d)).re := by
  rw [radialCompletedRemainder_eq_cubic_add_higher, inner_add_right, inner_smul_right]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [radialEuler_cubic_boundary_energy]
  simp only [Complex.mul_re]
  ring

/-- The new slope-energy term is genuinely nonnegative, from the raw source
scale. The retained value/curvature cross has no sign asserted. -/
theorem radialCompletedCubic_slope_energy_nonnegative (k N : ℕ) (d : Fin N → ℂ) :
    0 ≤ -2 * ((k : ℝ) + 1) * radialCompletedCubicScale k *
      Complex.normSq (radialEulerBoundaryJet d 1) := by
  have hb := radialCompletedCubicScale_neg k
  have hk : 0 < (k : ℝ) + 1 := by positivity
  exact mul_nonneg (by nlinarith) (Complex.normSq_nonneg _)

/-- The whole storage includes BOTH boundary degrees and their oriented
value/curvature cross, followed by the exact higher-source remainder. -/
theorem storage_one_eq_green_boundary_tower (k N : ℕ) (c : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    let d := radialCompletedValueCoefficients k c
    (storage k c 1).re =
      2 * ((k : ℝ) + 1) * radialCompletedEulerScale k *
        Complex.normSq (radialEulerBoundaryJet d 0) +
      4 * ((k : ℝ) + 1) * radialCompletedCubicScale k *
        (conj (radialEulerBoundaryJet d 0) * radialEulerBoundaryJet d 2).re -
      2 * ((k : ℝ) + 1) * radialCompletedCubicScale k *
        Complex.normSq (radialEulerBoundaryJet d 1) +
      4 * (inner ℂ (radialIncidentSynthesis k N d)
        (radialCompletedCubicRemainderSynthesis k N d)).re := by
  dsimp only
  rw [storage_one_eq_euler_boundary_add_remainder k N c hF hP,
    radialCompletedRemainder_pairing_eq_green_boundary, radialEulerBoundaryJet_zero]
  ring

/-- The EXACT original norm gate; the signed cross and the full remaining
source are both necessary. A positive slope term alone is not sufficient. -/
theorem radialReturnTransfer_norm_le_one_iff_green_boundary_tower (k N : ℕ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    ‖radialReturnTransfer k N‖ ≤ 1 ↔ ∀ d : Fin N → ℂ,
      -(((k : ℝ) + 1) / 2 * radialCompletedEulerScale k *
          Complex.normSq (radialEulerBoundaryJet d 0)) -
        ((k : ℝ) + 1) * radialCompletedCubicScale k *
          (conj (radialEulerBoundaryJet d 0) * radialEulerBoundaryJet d 2).re +
        ((k : ℝ) + 1) / 2 * radialCompletedCubicScale k *
          Complex.normSq (radialEulerBoundaryJet d 1) ≤
        (inner ℂ (radialIncidentSynthesis k N d) (radialCompletedCubicRemainderSynthesis k N d)).re := by
  rw [radialReturnTransfer_norm_le_one_iff_euler_remainder k N hF hP]
  apply forall_congr'
  intro d
  rw [radialCompletedRemainder_pairing_eq_green_boundary, ← radialEulerBoundaryJet_zero]
  constructor <;> intro h <;> nlinarith

/-- The same all-order contraction gate, with no cutoff uniform in N or
restriction of coefficient directions introduced by the boundary split. -/
theorem radialReturnTransfer_eventually_norm_le_one_iff_green_boundary_tower :
    (∀ N : ℕ, ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1) ↔
      ∀ N : ℕ, ∀ᶠ k : ℕ in atTop, ∀ d : Fin N → ℂ,
        -(((k : ℝ) + 1) / 2 * radialCompletedEulerScale k *
            Complex.normSq (radialEulerBoundaryJet d 0)) -
          ((k : ℝ) + 1) * radialCompletedCubicScale k *
            (conj (radialEulerBoundaryJet d 0) * radialEulerBoundaryJet d 2).re +
          ((k : ℝ) + 1) / 2 * radialCompletedCubicScale k *
            Complex.normSq (radialEulerBoundaryJet d 1) ≤
          (inner ℂ (radialIncidentSynthesis k N d)
            (radialCompletedCubicRemainderSynthesis k N d)).re := by
  constructor
  · intro h N
    filter_upwards [h N, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
      with k hk hreg
    exact (radialReturnTransfer_norm_le_one_iff_green_boundary_tower k N
      (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)).mp hk
  · intro h N
    filter_upwards [h N, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
      with k hk hreg
    exact (radialReturnTransfer_norm_le_one_iff_green_boundary_tower k N
      (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)).mpr hk

/-- On zero-value boundary data the cross and first boundary term vanish.
The exact higher correction still has to be compared with slope energy. -/
theorem storage_one_zero_value_eq_slope_add_higher (k N : ℕ) (d : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hd : radialEulerBoundaryJet d 0 = 0) :
    (storage k (radialCompletedInputCoefficients k d) 1).re =
      -2 * ((k : ℝ) + 1) * radialCompletedCubicScale k *
        Complex.normSq (radialEulerBoundaryJet d 1) +
      4 * (inner ℂ (radialIncidentSynthesis k N d)
        (radialCompletedCubicRemainderSynthesis k N d)).re := by
  have h := storage_one_eq_green_boundary_tower k N
    (radialCompletedInputCoefficients k d) hF hP
  dsimp only at h
  rw [radialCompletedValueCoefficients_input k N d hF hP, hd] at h
  simpa using h

/-- Zero boundary value AND slope leave only the exact higher-source pairing. -/
theorem storage_one_zero_value_slope_eq_higher (k N : ℕ) (d : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hd0 : radialEulerBoundaryJet d 0 = 0) (hd1 : radialEulerBoundaryJet d 1 = 0) :
    (storage k (radialCompletedInputCoefficients k d) 1).re =
      4 * (inner ℂ (radialIncidentSynthesis k N d)
        (radialCompletedCubicRemainderSynthesis k N d)).re := by
  rw [storage_one_zero_value_eq_slope_add_higher k N d hF hP hd0, hd1]
  simp

/-- Smallest second-boundary cancellation: no source parameter or target value
is used to choose these coefficients. -/
theorem radialEulerBoundaryJet_secondDifference_zero :
    radialEulerBoundaryJet (![1, -2, 1] : Fin 3 → ℂ) 0 = 0 ∧
      radialEulerBoundaryJet (![1, -2, 1] : Fin 3 → ℂ) 1 = 0 := by
  norm_num [radialEulerBoundaryJet, Fin.sum_univ_succ]

/-- Three-sample native canary. Both degree terms cancel, leaving exactly
this ordered combination of the full source slopes. No sign is asserted. -/
theorem storage_one_completed_secondDifference_eq_three_slopes (k : ℕ)
    (hF : ∀ i : Fin 3, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin 3, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k (radialCompletedInputCoefficients k (![1, -2, 1] : Fin 3 → ℂ)) 1).re =
      ((k : ℝ) + 1) / 15 *
        (5 * (radialCompletedSlope k 0).re - 4 * (radialCompletedSlope k 1).re +
          (radialCompletedSlope k 2).re) := by
  have hd0 := radialEulerBoundaryJet_secondDifference_zero.1
  have hd1 := radialEulerBoundaryJet_secondDifference_zero.2
  rw [storage_one_zero_value_slope_eq_higher k 3 _ hF hP hd0 hd1]
  have hi : inner ℂ (radialIncidentSynthesis k 3 ![1, -2, 1])
      (radialCompletedCubicRemainderSynthesis k 3 ![1, -2, 1]) =
      ((((k : ℝ) + 1) / 60 : ℝ) : ℂ) *
        (5 * radialCompletedSlope k 0 - 4 * radialCompletedSlope k 1 + radialCompletedSlope k 2) := by
    simp only [radialCompletedCubicRemainderSynthesis, radialIncidentSynthesis,
      LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
      one_mul, one_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, inner_completedNativeRadialChiralCauchyState,
      radialCompletedCubicRemainder, radialCompletedEulerRemainder]
    push_cast
    norm_num [map_ofNat]
    ring
  rw [hi]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, Complex.sub_re]
  norm_num
  ring


/-- Complete the scalar boundary square in the EXISTING complex norm, using
only the two fixed source curvatures. No new metric or Hilbert state is defined. -/
theorem radialCompleted_boundary_square (k N : ℕ) (d : Fin N → ℂ) :
    2 * ((k : ℝ) + 1) * radialCompletedEulerScale k *
        Complex.normSq (radialEulerBoundaryJet d 0) +
      4 * ((k : ℝ) + 1) * radialCompletedCubicScale k *
        (conj (radialEulerBoundaryJet d 0) * radialEulerBoundaryJet d 2).re =
      2 * ((k : ℝ) + 1) * radialCompletedEulerScale k *
        Complex.normSq (radialEulerBoundaryJet d 0 +
          ((radialCompletedCubicScale k / radialCompletedEulerScale k : ℝ) : ℂ) *
            radialEulerBoundaryJet d 2) -
      2 * ((k : ℝ) + 1) * radialCompletedCubicScale k ^ 2 /
        radialCompletedEulerScale k * Complex.normSq (radialEulerBoundaryJet d 2) := by
  have ha := (radialCompletedEulerScale_pos k).ne'
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im, zero_mul, add_zero, sub_zero]
  field_simp [ha]
  ring

/-- Two nonnegative boundary energies plus the EXACT signed higher defect.
The final two terms have no nonnegative sign claimed. -/
theorem storage_one_eq_green_squares_plus_signed_defect (k N : ℕ) (c : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    let d := radialCompletedValueCoefficients k c
    (storage k c 1).re =
      2 * ((k : ℝ) + 1) * radialCompletedEulerScale k *
        Complex.normSq (radialEulerBoundaryJet d 0 +
          ((radialCompletedCubicScale k / radialCompletedEulerScale k : ℝ) : ℂ) *
            radialEulerBoundaryJet d 2) -
      2 * ((k : ℝ) + 1) * radialCompletedCubicScale k *
        Complex.normSq (radialEulerBoundaryJet d 1) +
      4 * (inner ℂ (radialIncidentSynthesis k N d)
        (radialCompletedCubicRemainderSynthesis k N d)).re -
      2 * ((k : ℝ) + 1) * radialCompletedCubicScale k ^ 2 /
        radialCompletedEulerScale k * Complex.normSq (radialEulerBoundaryJet d 2) := by
  dsimp only
  rw [storage_one_eq_green_boundary_tower k N c hF hP,
    radialCompleted_boundary_square]
  ring


end
end CarrySelfAdjointOperator.ChiralReturn

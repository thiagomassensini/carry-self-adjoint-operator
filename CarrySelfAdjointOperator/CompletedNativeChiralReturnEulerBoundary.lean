import CarrySelfAdjointOperator.CompletedNativeChiralReturnFiniteTransfer
import CarrySelfAdjointOperator.CompletedNativeXiCosineMoments

/-!
# Euler boundary energy and the exact completed-source remainder

The original Cauchy half densities have a degree generator whose Hermitian
part is a boundary readout. The completed source is split into this degree
term, with its own raw characteristic curvature, and its EXACT remainder.
Neither the source nor the Cauchy metric is changed. Positivity of the
boundary term does not control the retained remainder.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- Degree action on the original half-density monomial coefficients. -/
def radialEulerSynthesis (k N : ℕ) (d : Fin N → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis k N (fun i => d i * ((i + 1 : ℕ) : ℂ))

/-- Complete polarization of the Euler boundary form, with independent data.
The Cauchy denominator cancels against the sum of the two native degrees. -/
theorem radialEuler_boundary_polarized (k N : ℕ) (d e : Fin N → ℂ) :
    inner ℂ (radialIncidentSynthesis k N d) (radialEulerSynthesis k N e) +
      inner ℂ (radialEulerSynthesis k N d) (radialIncidentSynthesis k N e) =
      ((k : ℝ) + 1 : ℂ) * conj (∑ i, d i) * (∑ i, e i) := by
  classical
  have hg (i j : Fin N) : inner ℂ (completedNativeRadialChiralCauchyState k i)
      (completedNativeRadialChiralCauchyState k j) =
      ((k : ℝ) + 1 : ℂ) / (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℂ) := by
    rw [inner_completedNativeRadialChiralCauchyState]
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    push_cast
    rfl
  simp only [radialEulerSynthesis, radialIncidentSynthesis, LinearMap.coe_mk,
    AddHom.coe_mk, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    hg, map_mul, map_natCast,
    ← Finset.sum_add_distrib, map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (i : ℕ) + (j : ℕ) + 2 ≠ 0 by omega)
  push_cast at h ⊢
  ring_nf at h ⊢
  field_simp [h]
  all_goals ring

/-- The symmetric part of the degree generator is the endpoint energy.
It has rank one, so cancellation at the boundary has no strictly positive
control from this term alone. -/
theorem radialEuler_boundary_energy (k N : ℕ) (d : Fin N → ℂ) :
    (inner ℂ (radialIncidentSynthesis k N d) (radialEulerSynthesis k N d)).re =
      ((k : ℝ) + 1) / 2 * Complex.normSq (∑ i, d i) := by
  have h := congrArg Complex.re (radialEuler_boundary_polarized k N d d)
  have hc := congrArg Complex.re (inner_conj_symm
    (radialIncidentSynthesis k N d) (radialEulerSynthesis k N d))
  simp only [Complex.conj_re] at hc
  rw [show ((k : ℝ) + 1 : ℂ) * conj (∑ i, d i) * (∑ i, d i) =
      ((k : ℝ) + 1 : ℂ) * (Complex.normSq (∑ i, d i) : ℂ) by
        rw [Complex.normSq_eq_conj_mul_self]; ring] at h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, mul_zero, sub_zero] at h
  linarith

/-- The exact completed source's transverse slope, BEFORE moment identification. -/
def radialCompletedSlope (k n : ℕ) : ℂ :=
  -Complex.I * completedNativeOperatorLogDerivative
    (canonicalCompletedC3RadialTiltPoint k n)

/-- Original completed value amplitudes; no tail or completion is removed. -/
def radialCompletedValueCoefficients (k : ℕ) {N : ℕ} (c : Fin N → ℂ) : Fin N → ℂ :=
  fun i => c i * completedNativeOperatorCharacteristic
    (canonicalCompletedC3RadialTiltPoint k i) /
    completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)

/-- Source-derived degree scale: raw curvature divided by the native radial
scale. It is not chosen from a target Gram or from canonical moments. -/
def radialCompletedEulerScale (k : ℕ) : ℝ :=
  (-iteratedDeriv 2 completedNativeOperatorCharacteristic 0 /
    completedNativeOperatorCharacteristic 0).re / ((k : ℝ) + 1)

/-- The full nonlinear source remainder is retained by subtraction of the
source's own degree term. It is not replaced by a Taylor truncation. -/
def radialCompletedEulerRemainder (k n : ℕ) : ℂ :=
  radialCompletedSlope k n - (radialCompletedEulerScale k : ℂ) * ((n + 1 : ℕ) : ℂ)

/-- Full synthesis of the remaining coefficients in the SAME Cauchy carrier. -/
def radialCompletedRemainderSynthesis (k N : ℕ) (d : Fin N → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis k N (fun i => d i * radialCompletedEulerRemainder k i)

/-- The centered raw curvature is the ratio of two positive source integrals.
These are moments of the upstream theta cosine kernel, NOT the canonical
logarithmic moment sequence. -/
theorem radialCompletedEulerScale_eq_sourceIntegralRatio (k : ℕ) :
    radialCompletedEulerScale k =
      (completedNativeXiCosineMoment 1 / completedNativeXiCosineMoment 0) /
        ((k : ℝ) + 1) := by
  have h0 : completedNativeOperatorCharacteristic 0 = (completedNativeXiCosineMoment 0 : ℂ) := by
    have ha : completedNativeOperatorCharacteristic 0 =
        (completedNativeXiCosineTransformReal 0 : ℂ) := by
      simpa [completedNativeXiCosineTransformReal] using
        XiThetaCosine.completedNative_eq_xiCosineKernel 0
    rw [ha, completedNativeXiCosineTransformReal_zero]
  unfold radialCompletedEulerScale
  rw [iteratedDeriv_two_completedNativeOperatorCharacteristic_zero, h0]
  simp

/-- Strictly positive degree scale from the raw positive source integrals. -/
theorem radialCompletedEulerScale_pos (k : ℕ) : 0 < radialCompletedEulerScale k := by
  rw [radialCompletedEulerScale_eq_sourceIntegralRatio]
  exact div_pos (div_pos (completedNativeXiCosineMoment_pos 1)
    (completedNativeXiCosineMoment_pos 0)) (by positivity)

/-- The completed value synthesis is literally the original Cauchy synthesis. -/
theorem sourceValue_eq_completedCoefficients (k N : ℕ) (c : Fin N → ℂ) :
    sourceValue k c 1 = radialIncidentSynthesis k N (radialCompletedValueCoefficients k c) := by
  simp [sourceValue, radialIncidentSynthesis, radialCompletedValueCoefficients]

/-- The complete companion equals the exact slope action on the complete
value amplitudes. Only the original nonzero F denominators are required. -/
theorem sourceCompanion_eq_completedSlope (k N : ℕ) (c : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    sourceCompanion k c 1 = Complex.I • radialIncidentSynthesis k N
      (fun i => radialCompletedValueCoefficients k c i * radialCompletedSlope k i) := by
  simp only [sourceCompanion, Complex.ofReal_one, one_pow, mul_one,
    radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold radialCompletedValueCoefficients radialCompletedSlope completedNativeOperatorLogDerivative
  field_simp [hF i]
  simp [Complex.I_sq, neg_div]

/-- Exact division into degree term and nonlinear remainder at vector level,
prior to scalarization and for arbitrary coefficient data. -/
theorem radialCompletedSlopeSynthesis_eq_euler_add_remainder (k N : ℕ) (d : Fin N → ℂ) :
    radialIncidentSynthesis k N (fun i => d i * radialCompletedSlope k i) =
      (radialCompletedEulerScale k : ℂ) • radialEulerSynthesis k N d +
        radialCompletedRemainderSynthesis k N d := by
  simp only [radialEulerSynthesis, radialCompletedRemainderSynthesis,
    radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, ← add_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold radialCompletedEulerRemainder
  ring

/-- The completed storage is boundary energy PLUS its exact signed nonlinear
remainder. Independent synthesis, completion and interference are retained. -/
theorem storage_one_eq_euler_boundary_add_remainder (k N : ℕ) (c : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k c 1).re =
      2 * ((k : ℝ) + 1) * radialCompletedEulerScale k *
        Complex.normSq (∑ i, radialCompletedValueCoefficients k c i) +
      4 * (inner ℂ
        (radialIncidentSynthesis k N (radialCompletedValueCoefficients k c))
        (radialCompletedRemainderSynthesis k N (radialCompletedValueCoefficients k c))).re := by
  rw [storage_re_eq_source_cross k c 1 hP, sourceValue_eq_completedCoefficients,
    sourceCompanion_eq_completedSlope k N c hF,
    radialCompletedSlopeSynthesis_eq_euler_add_remainder, inner_smul_right,
    inner_add_right, inner_smul_right]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [radialEuler_boundary_energy]
  ring

/-- The Euler boundary contribution is positive semidefinite on every
finite source family. This alone is NOT storage positivity. -/
theorem radialCompletedEuler_boundary_nonnegative (k N : ℕ) (d : Fin N → ℂ) :
    0 ≤ 2 * ((k : ℝ) + 1) * radialCompletedEulerScale k * Complex.normSq (∑ i, d i) := by
  exact mul_nonneg
    (mul_pos (mul_pos (by norm_num) (by positivity)) (radialCompletedEulerScale_pos k)).le
    (Complex.normSq_nonneg _)

/-- Original source-amplitude coordinate change, with no kernel fitting. -/
def radialCompletedInputCoefficients (k : ℕ) {N : ℕ} (d : Fin N → ℂ) : Fin N → ℂ :=
  fun i => d i * completedNativePositiveHermiteBiehlerCoordinate
    (canonicalCompletedC3RadialTiltPoint k i) /
    completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)

/-- These coordinates are invertible solely on the existing regular source. -/
theorem radialCompletedValueCoefficients_input (k N : ℕ) (d : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    radialCompletedValueCoefficients k (radialCompletedInputCoefficients k d) = d := by
  funext i
  unfold radialCompletedValueCoefficients radialCompletedInputCoefficients
  field_simp [hF i, hP i]

/-- Exact quantitative remainder gate; nonnegative remainder on ALL vectors
is not imposed. The negative boundary-energy allowance is kept. -/
theorem radialReturnTransfer_norm_le_one_iff_euler_remainder (k N : ℕ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    ‖radialReturnTransfer k N‖ ≤ 1 ↔ ∀ d : Fin N → ℂ,
      -(((k : ℝ) + 1) / 2 * radialCompletedEulerScale k * Complex.normSq (∑ i, d i)) ≤
        (inner ℂ (radialIncidentSynthesis k N d) (radialCompletedRemainderSynthesis k N d)).re := by
  rw [radialReturnTransfer_norm_le_one_iff_storage]
  constructor
  · intro h d
    have hs := h (radialCompletedInputCoefficients k d)
    have he := storage_one_eq_euler_boundary_add_remainder k N
      (radialCompletedInputCoefficients k d) hF hP
    rw [radialCompletedValueCoefficients_input k N d hF hP] at he
    rw [he] at hs
    nlinarith
  · intro h c
    rw [storage_one_eq_euler_boundary_add_remainder k N c hF hP]
    have hd := h (radialCompletedValueCoefficients k c)
    nlinarith

/-- Keep the original all-order quantifiers and the SAME exact source remainder. -/
theorem radialReturnTransfer_eventually_norm_le_one_iff_euler_remainder :
    (∀ N : ℕ, ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1) ↔
      ∀ N : ℕ, ∀ᶠ k : ℕ in atTop, ∀ d : Fin N → ℂ,
        -(((k : ℝ) + 1) / 2 * radialCompletedEulerScale k * Complex.normSq (∑ i, d i)) ≤
          (inner ℂ (radialIncidentSynthesis k N d) (radialCompletedRemainderSynthesis k N d)).re := by
  constructor
  · intro h N
    filter_upwards [h N, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
      with k hk hreg
    exact (radialReturnTransfer_norm_le_one_iff_euler_remainder k N
      (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)).mp hk
  · intro h N
    filter_upwards [h N, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
      with k hk hreg
    exact (radialReturnTransfer_norm_le_one_iff_euler_remainder k N
      (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)).mpr hk

/-- On boundary-cancelling data the positive degree contribution disappears. -/
theorem radialEuler_boundary_energy_zero_of_sum_zero (k N : ℕ) (d : Fin N → ℂ)
    (hd : ∑ i, d i = 0) :
    (inner ℂ (radialIncidentSynthesis k N d) (radialEulerSynthesis k N d)).re = 0 := by
  rw [radialEuler_boundary_energy, hd]
  simp

/-- The smallest cancellation direction retains the exact two native slopes.
The Euler scale cancels; no affine approximation is used. -/
theorem radialCompletedRemainder_opposite_pairing (k : ℕ) :
    inner ℂ (radialIncidentSynthesis k 2 ![1, -1])
      (radialCompletedRemainderSynthesis k 2 ![1, -1]) =
        ((((k : ℝ) + 1) / 12 : ℝ) : ℂ) *
          (2 * radialCompletedSlope k 0 - radialCompletedSlope k 1) := by
  simp only [radialCompletedRemainderSynthesis, radialIncidentSynthesis,
    LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, neg_one_mul, one_smul, neg_smul,
    ← sub_eq_add_neg, inner_sub_left, inner_sub_right, inner_smul_right,
    inner_completedNativeRadialChiralCauchyState, radialCompletedEulerRemainder]
  push_cast
  norm_num
  ring

/-- Exact first cancellation canary for the ACTUAL completed source; its
sign is not inferred from the strictly positive Euler boundary coefficient. -/
theorem storage_one_completed_opposite_eq_two_slopes (k : ℕ)
    (hF : ∀ i : Fin 2, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin 2, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k (radialCompletedInputCoefficients k (![1, -1] : Fin 2 → ℂ)) 1).re =
      ((k : ℝ) + 1) / 3 *
        (2 * (radialCompletedSlope k 0).re - (radialCompletedSlope k 1).re) := by
  rw [storage_one_eq_euler_boundary_add_remainder k 2 _ hF hP,
    radialCompletedValueCoefficients_input k 2 _ hF hP, radialCompletedRemainder_opposite_pairing]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_neg_cancel, Complex.normSq_zero, mul_zero, zero_add,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_re]
  norm_num
  ring

/-- Necessary native source inequality on the first genuine cancelling family. -/
theorem radialReturnTransfer_two_norm_le_one_implies_slope_inequality (k : ℕ)
    (hF : ∀ i : Fin 2, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin 2, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hT : ‖radialReturnTransfer k 2‖ ≤ 1) :
    0 ≤ 2 * (radialCompletedSlope k 0).re - (radialCompletedSlope k 1).re := by
  have h := (radialReturnTransfer_norm_le_one_iff_storage k 2).mp hT
    (radialCompletedInputCoefficients k (![1, -1] : Fin 2 → ℂ))
  rw [storage_one_completed_opposite_eq_two_slopes k hF hP] at h
  exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < ((k : ℝ) + 1) / 3)).mp h

end
end CarrySelfAdjointOperator.ChiralReturn

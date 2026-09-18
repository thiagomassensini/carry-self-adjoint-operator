import CarrySelfAdjointOperator.CompletedNativeChiralTwoPointControl
import CarrySelfAdjointOperator.CompletedNativeCentralChiralQuotientCurvature
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy
import CarrySelfAdjointOperator.CompletedC3FullWronskianChiralDslope

/-!
# Accumulated return balance on the existing radial Cauchy carrier

The internal coordinate `r` belongs to the unit-interval Cauchy realization.
It is neither native height nor the material carry clock. The two polynomial
readouts use the same coefficients and the already completed chiral quotient.
Their accumulated signed balance is exactly a weighted synthesis in the
existing carrier. No sign is built into this balance.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace Matrix

namespace CarrySelfAdjointOperator.ChiralReturn

open Filter
noncomputable section
set_option autoImplicit false

/-- Incident polynomial of the existing Cauchy half-density family. -/
def incident {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : ℂ :=
  ∑ i, c i * (r : ℂ) ^ (i : ℕ)

/-- The same polynomial coefficients after the native chiral multiplier. -/
def returned (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : ℂ :=
  incident (fun i => c i * completedNativeHermiteBiehlerChiralQuotient
    (canonicalCompletedC3RadialTiltPoint k i)) r

/-- Accumulated signed balance; its coefficients are the existing defect
Gram, not a new proposed kernel. Its value is real on the real `r` axis. -/
def storage (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ∑ j, conj (c i) * c j *
    canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N i j *
      (r : ℂ) ^ ((i : ℕ) + (j : ℕ) + 2)

/-- Cancellation of the Cauchy denominator by its native degree weight. -/
theorem degree_mul_defect_entry (k N : ℕ) (i j : Fin N) :
    (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℂ) *
        canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N i j =
      ((k : ℝ) + 1 : ℂ) *
        (1 - conj (completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k i)) *
          completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k j)) := by
  rw [canonicalCompletedNativeRadialChiralMultiplierDefectMatrix_apply]
  push_cast
  have h : (i : ℂ) + (j : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show (i : ℕ) + (j : ℕ) + 2 ≠ 0 by omega)
  field_simp

/-- All interference terms are preserved in the weighted synthesis. -/
theorem storage_eq_quadratic (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    storage k c r =
      star (fun i => c i * (r : ℂ) ^ ((i : ℕ) + 1)) ⬝ᵥ
        (canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N *ᵥ
          (fun i => c i * (r : ℂ) ^ ((i : ℕ) + 1))) := by
  simp only [storage, dotProduct, Matrix.mulVec, Pi.star_apply,
    star_mul, star_pow, Complex.star_def, Complex.conj_ofReal,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show (i : ℕ) + (j : ℕ) + 2 =
      ((i : ℕ) + 1) + ((j : ℕ) + 1) by omega, pow_add]
  ring

/-- Real accumulated balance in the unchanged Hilbert carrier. -/
theorem storage_re_eq_norm_balance (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ) :
    (storage k c r).re =
      ‖∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1)) •
        completedNativeRadialChiralCauchyState k i‖ ^ 2 -
      ‖∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1)) •
        completedNativeRadialChiralMultiplierState k i‖ ^ 2 := by
  rw [storage_eq_quadratic,
    canonicalCompletedNativeRadialChiralMultiplierDefectMatrix,
    Matrix.sub_mulVec, dotProduct_sub,
    Matrix.star_dotProduct_gram_mulVec,
    Matrix.star_dotProduct_gram_mulVec]
  rw [Complex.sub_re]
  exact congrArg₂ (fun a b : ℝ => a - b)
    (inner_self_eq_norm_sq (𝕜 := ℂ) _) (inner_self_eq_norm_sq (𝕜 := ℂ) _)

@[simp] theorem storage_zero (k : ℕ) {N : ℕ} (c : Fin N → ℂ) :
    storage k c 0 = 0 := by
  simp [storage]

/-- Local balance law along the internal Cauchy coordinate. The right hand
side is signed; it is not assumed to be a dissipated nonnegative energy. -/
theorem hasDerivAt_storage (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    HasDerivAt (storage k c)
      (((k : ℝ) + 1 : ℂ) * (r : ℂ) *
        ((Complex.normSq (incident c r) : ℂ) -
          (Complex.normSq (returned k c r) : ℂ))) r := by
  have hterm (i j : Fin N) :
      HasDerivAt
        (fun x : ℝ => conj (c i) * c j *
          canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N i j *
            (x : ℂ) ^ ((i : ℕ) + (j : ℕ) + 2))
        (conj (c i) * c j * ((k : ℝ) + 1 : ℂ) *
          (1 - conj (completedNativeHermiteBiehlerChiralQuotient
              (canonicalCompletedC3RadialTiltPoint k i)) *
            completedNativeHermiteBiehlerChiralQuotient
              (canonicalCompletedC3RadialTiltPoint k j)) *
          (r : ℂ) ^ ((i : ℕ) + (j : ℕ) + 1)) r := by
    have h := (((hasDerivAt_id (r : ℂ)).pow
      ((i : ℕ) + (j : ℕ) + 2)).const_mul
        (conj (c i) * c j *
          canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N i j)).comp_ofReal
    convert h using 1 <;> try rfl
    simp only [id_eq, show (i : ℕ) + (j : ℕ) + 2 - 1 =
      (i : ℕ) + (j : ℕ) + 1 by omega, mul_one]
    rw [show conj (c i) * c j *
        canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N i j *
          ((((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℂ) *
            (r : ℂ) ^ ((i : ℕ) + (j : ℕ) + 1)) =
        conj (c i) * c j *
          ((((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℂ) *
            canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N i j) *
              (r : ℂ) ^ ((i : ℕ) + (j : ℕ) + 1) by ring,
      degree_mul_defect_entry]
    ring
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => HasDerivAt.sum (u := Finset.univ) (fun j _ => hterm i j))
  convert hsum using 1 <;> try rfl
  · ext x
    simp [storage]
  simp only [Complex.normSq_eq_conj_mul_self, incident, returned,
    map_sum, map_mul, map_pow, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum,
    mul_sub, pow_add, pow_one, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Integrated balance, with the zero endpoint retained. -/
theorem integral_flux_eq_storage (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    (∫ x in (0 : ℝ)..r, ((k : ℝ) + 1 : ℂ) * (x : ℂ) *
      ((Complex.normSq (incident c x) : ℂ) -
        (Complex.normSq (returned k c x) : ℂ))) = storage k c r := by
  have hc : Continuous (fun x : ℝ => ((k : ℝ) + 1 : ℂ) * (x : ℂ) *
      ((Complex.normSq (incident c x) : ℂ) -
        (Complex.normSq (returned k c x) : ℂ))) := by
    unfold returned incident
    fun_prop
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := r) (fun x _ => hasDerivAt_storage k c x)
    (hc.intervalIntegrable 0 r)

/-- Two opposite incident coefficients cancel at the upper endpoint. Their
returned coefficients retain the difference of the two native quotients. -/
theorem opposite_endpoint_flux (k : ℕ) :
    (deriv (storage k ![1, -1]) 1).re =
      -((k : ℝ) + 1) * Complex.normSq
        (completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k 0) -
          completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k 1)) := by
  rw [(hasDerivAt_storage k ![1, -1] 1).deriv]
  simp [incident, returned, Fin.sum_univ_two, Complex.mul_re]
  ring

/-- Reinsert the exact existing projective amplitude. The accumulated
balance at the full interval is twice the native quadratic kernel readout;
regularity is used solely for the already proved scalar identification. -/
theorem storage_one_eq_native_quadratic (k N : ℕ) (c : Fin N → ℂ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈ completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    storage k (fun i => c i * completedNativeNormalizedPositiveChiralAmplitude
        (canonicalCompletedC3RadialTiltPoint k i)) 1 =
      2 * (star c ⬝ᵥ (canonicalCompletedNativeRadialDslopeSampleMatrix k N *ᵥ c)) := by
  rw [canonicalCompletedNativeRadialDslopeSampleMatrix_eq_pickCongruence k N hregular,
    canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect]
  simp only [storage, Complex.ofReal_one, one_pow, mul_one,
    dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.mul_diagonal,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Pi.star_apply,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    Complex.star_def, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual completed quotient varies between the first two samples.
This uses the existing central derivative and strict native moment, not a
numerically chosen or freely postulated reflection coefficient. -/
theorem native_quotient_two_samples_ne_eventually :
    ∀ᶠ k : ℕ in atTop,
      completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k 1) ≠
        completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k 0) := by
  have hq := hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero
  have hq2 : HasDerivAt completedNativeHermiteBiehlerChiralQuotient
      (-4 * Complex.I * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))
      ((2 : ℂ) * 0) := by simpa using hq
  have hd := (hq2.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul 2)).sub hq
  have hderivative :
      (-4 * Complex.I * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) *
          (2 * 1) -
        (-4 * Complex.I * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) ≠ 0 := by
    rw [show (-4 * Complex.I * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) *
        (2 * 1) - (-4 * Complex.I * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) =
      -4 * Complex.I * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne')
  have hne := hd.eventually_ne (c := (0 : ℂ)) hderivative
  have hp : Tendsto (fun k => canonicalCompletedC3RadialTiltPoint k 0)
      atTop (nhdsWithin 0 ({0} : Set ℂ)ᶜ) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨canonicalCompletedC3RadialTiltPoint_tendsto_zero 0,
        Filter.Eventually.of_forall fun k => by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
            (fun h : canonicalCompletedC3RadialTiltPoint k 0 = 0 =>
              canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0
                (by rw [h]; rfl))⟩
  filter_upwards [hp.eventually hne] with k hk
  have hpoint : (2 : ℂ) * canonicalCompletedC3RadialTiltPoint k 0 =
      canonicalCompletedC3RadialTiltPoint k 1 := by
    simp [canonicalCompletedC3RadialTiltPoint]
  change completedNativeHermiteBiehlerChiralQuotient
      ((2 : ℂ) * canonicalCompletedC3RadialTiltPoint k 0) -
    completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0 at hk
  rw [hpoint, sub_ne_zero] at hk
  exact hk

/-- On the same concrete two-sample family, accumulated energy is
nonnegative at every internal radius, while its endpoint flux is negative.
Thus the already proved integrated contraction is compatible with local
return exceeding local incidence. This is not an all-order contraction. -/
theorem two_point_storage_nonnegative_but_endpoint_flux_negative :
    ∀ᶠ k : ℕ in atTop,
      (∀ r : ℝ, 0 ≤ (storage k ![1, -1] r).re) ∧
        (deriv (storage k ![1, -1]) 1).re < 0 := by
  filter_upwards [canonicalCompletedNativeChiralTwoPoint_contractive_eventually,
    native_quotient_two_samples_ne_eventually] with k hk hne
  constructor
  · intro r
    rw [storage_re_eq_norm_balance]
    exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (hk (fun i : Fin 2 => ![1, -1] i * (r : ℂ) ^ ((i : ℕ) + 1))))
  · rw [opposite_endpoint_flux]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity))
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hne.symm))

theorem chiralMultiplierContractiveAt_iff_storage_one_nonnegative
    (k N : ℕ) :
    CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k N ↔
      ∀ c : Fin N → ℂ, 0 ≤ (storage k c 1).re := by
  constructor
  · intro h c
    rw [storage_re_eq_norm_balance]
    simp only [Complex.ofReal_one, one_pow, mul_one]
    exact sub_nonneg.mpr
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h c))
  · intro h c
    have hs :
        ‖∑ i, c i • completedNativeRadialChiralMultiplierState k i‖ ^ 2 ≤
          ‖∑ i, c i • completedNativeRadialChiralCauchyState k i‖ ^ 2 := by
      have hstorage := h c
      rw [storage_re_eq_norm_balance] at hstorage
      simpa only [Complex.ofReal_one, one_pow, mul_one] using
        (sub_nonneg.mp hstorage)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem chiralMultiplierEventuallyContractive_iff_storage_one_eventually_nonnegative :
    CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive ↔
      ∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
        ∀ c : Fin N → ℂ, 0 ≤ (storage k c 1).re := by
  constructor
  · intro h N
    filter_upwards [h N] with k hk
    exact
      (chiralMultiplierContractiveAt_iff_storage_one_nonnegative k N).mp hk
  · intro h N
    filter_upwards [h N] with k hk
    exact
      (chiralMultiplierContractiveAt_iff_storage_one_nonnegative k N).mpr hk

def fullWronskianRegularizedChiralSampleMatrix
    (M k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    Complex.I *
      (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
          M
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j) -
       canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
          M
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)) /
      (canonicalCompletedC3RadialTiltPoint k j -
        conj (canonicalCompletedC3RadialTiltPoint k i))

theorem fullWronskianRegularizedChiralSampleMatrix_eq_dslope
    (M k N : ℕ)
    (hstrip : ∀ i : Fin N,
      operatorHeightParameter
          (canonicalCompletedC3RadialTiltPoint k i) ∈
        CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hF : ∀ i : Fin N,
      completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    fullWronskianRegularizedChiralSampleMatrix M k N =
      canonicalCompletedNativeRadialDslopeSampleMatrix k N := by
  ext i j
  unfold fullWronskianRegularizedChiralSampleMatrix
    canonicalCompletedNativeRadialDslopeSampleMatrix
  exact
    (canonicalCompletedNativePolarizedDslopeKernel_eq_chiralDifference_div
      M
      (z := canonicalCompletedC3RadialTiltPoint k i)
      (w := canonicalCompletedC3RadialTiltPoint k j)
      (hzStrip := hstrip i)
      (hwStrip := hstrip j)
      (hzF := hF i)
      (hwF := hF j)
      (hsep := sub_ne_zero.mp
        (canonicalCompletedC3RadialTilt_separation_ne_zero k i j))).symm

theorem storage_one_eventually_nonnegative_iff_dslope :
    (∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
      ∀ c : Fin N → ℂ, 0 ≤ (storage k c 1).re) ↔
      CanonicalCompletedNativeRadialDslopeEventuallyPosSemidefinite := by
  calc
    (∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
      ∀ c : Fin N → ℂ, 0 ≤ (storage k c 1).re) ↔
        CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive :=
      chiralMultiplierEventuallyContractive_iff_storage_one_eventually_nonnegative.symm
    _ ↔ CanonicalCompletedNativeRadialDslopeEventuallyPosSemidefinite :=
      canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_dslope

end
end CarrySelfAdjointOperator.ChiralReturn

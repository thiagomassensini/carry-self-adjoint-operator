import CarrySelfAdjointOperator.CompletedNativeAdjacentClockCorrectedLedger
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Exact finite transfer of the completed chiral return

The incident span carries the original Cauchy Hilbert norm. Coefficients are
recovered from the ORIGINAL half-density monomials, independently of the
returned quotient and of any target kernel. The return is the original full
finite synthesis. Finite-dimensional continuity is not contractivity.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace unitInterval
open Filter Topology MeasureTheory
noncomputable section
set_option autoImplicit false

/-- Actual incident synthesis at internal radius one, before observation. -/
def radialIncidentSynthesis (k N : ℕ) :
    (Fin N → ℂ) →ₗ[ℂ] CanonicalCompletedNativeChiralCauchyCarrier where
  toFun c := ∑ i, c i • completedNativeRadialChiralCauchyState k i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

/-- Actual return: the completed source quotient, not interpolation data. -/
def radialReturnedSynthesis (k N : ℕ) :
    (Fin N → ℂ) →ₗ[ℂ] CanonicalCompletedNativeChiralCauchyCarrier where
  toFun c := ∑ i, c i • completedNativeRadialChiralMultiplierState k i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

private theorem halfDensity_synthesis_eq_zero {N : ℕ} (c : Fin N → ℂ)
    (h : (∑ i, c i • completedNativeChiralCauchyFeature i) = 0) : c = 0 := by
  classical
  let f : C(unitInterval, ℂ) := ∑ i, c i • completedNativeChiralCauchyContinuousFeature i
  let H : ℝ → ℂ := fun x => (Real.sqrt x : ℂ) * ∑ i, c i * (x : ℂ) ^ (i : ℕ)
  have hH : Continuous H := by unfold H; fun_prop
  have hf (x : unitInterval) : f x = H x := by
    simp only [f, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      completedNativeChiralCauchyContinuousFeature, smul_eq_mul, H]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change c i * ((Real.sqrt (x : ℝ) : ℂ) * (x : ℂ) ^ (i : ℕ)) = _
    ring
  have hLp : ContinuousMap.toLp 2 volume ℂ f = 0 := by
    simpa only [f, map_sum, map_smul, completedNativeChiralCauchyFeature] using h
  have hsub : ∀ᵐ x : unitInterval, H x = 0 := by
    have hae := (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f).symm
    rw [hLp] at hae
    filter_upwards [hae, Lp.coeFn_zero ℂ 2 (volume : Measure unitInterval)] with x hx hz
    rw [← hf x, hx, hz]
    rfl
  have hae : H =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun _ => 0) := by
    rw [← unitInterval.measurePreserving_coe.map_eq]
    exact (ae_map_iff unitInterval.measurePreserving_coe.measurable.aemeasurable
      (measurableSet_eq_fun hH.measurable measurable_const)).mpr hsub
  have hpoint := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ)
    (by norm_num : (0 : ℝ) ≠ 1) hae hH.continuousOn continuous_const.continuousOn
  let p : Polynomial ℂ := ∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
  have hroot {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : p.IsRoot (x : ℂ) := by
    have hzero := hpoint ⟨hx.1.le, hx.2.le⟩
    have hsqrt : (Real.sqrt x : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hx.1).ne'
    have hsum : (∑ i, c i * (x : ℂ) ^ (i : ℕ)) = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left hsqrt
    simpa only [p, Polynomial.IsRoot, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using hsum
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).image
      (Complex.ofReal_injective.injOn)).mono
    rintro z ⟨x, hx, rfl⟩
    exact hroot hx
  funext i
  have hi := congrArg (fun q : Polynomial ℂ => q.coeff (i : ℕ)) hp
  simpa [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, ← Fin.ext_iff] using hi

/-- The incident ledger loses no coefficient, at any finite order/cutoff. -/
theorem radialIncidentSynthesis_injective (k N : ℕ) :
    Function.Injective (radialIncidentSynthesis k N) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  have hs : (((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < (k : ℝ) + 1)).ne'
  have he : radialIncidentSynthesis k N c =
      (((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ)) •
        (∑ i, c i • completedNativeChiralCauchyFeature i) := by
    simp only [radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
      completedNativeRadialChiralCauchyState, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  rw [he] at hc
  exact halfDensity_synthesis_eq_zero c ((smul_eq_zero.mp hc).resolve_left hs)

/-- Intrinsic finite incident span with the UNCHANGED Cauchy norm. -/
abbrev RadialIncidentSpan (k N : ℕ) := (radialIncidentSynthesis k N).range

/-- Recover the unique incident coefficients BEFORE applying the return.
This inverse depends only on the original monomial features, not the quotient. -/
def radialIncidentCoordinates (k N : ℕ) :
    RadialIncidentSpan k N ≃ₗ[ℂ] (Fin N → ℂ) :=
  (LinearEquiv.ofInjective (radialIncidentSynthesis k N)
    (radialIncidentSynthesis_injective k N)).symm

/-- Source-generated incident vector in its actual span. -/
def radialIncidentVector (k N : ℕ) (c : Fin N → ℂ) : RadialIncidentSpan k N :=
  (radialIncidentCoordinates k N).symm c

@[simp] theorem radialIncidentVector_coe (k N : ℕ) (c : Fin N → ℂ) :
    (radialIncidentVector k N c : CanonicalCompletedNativeChiralCauchyCarrier) =
      radialIncidentSynthesis k N c := by
  rfl

@[simp] theorem radialIncidentVector_norm (k N : ℕ) (c : Fin N → ℂ) :
    ‖radialIncidentVector k N c‖ = ‖radialIncidentSynthesis k N c‖ := by
  change ‖(radialIncidentVector k N c : CanonicalCompletedNativeChiralCauchyCarrier)‖ = _
  rw [radialIncidentVector_coe]

/-- Unique source transfer on the finite incident span. Continuity follows
from finite dimension, not from any asserted contraction or positive kernel. -/
def radialReturnTransfer (k N : ℕ) :
    RadialIncidentSpan k N →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier :=
  letI := (radialIncidentSynthesis k N).finiteDimensional_range
  ((radialReturnedSynthesis k N).comp (radialIncidentCoordinates k N).toLinearMap).toContinuousLinearMap

/-- Exact action on ALL complete incident syntheses. -/
theorem radialReturnTransfer_exact (k N : ℕ) (c : Fin N → ℂ) :
    radialReturnTransfer k N (radialIncidentVector k N c) =
      radialReturnedSynthesis k N c := by
  change radialReturnedSynthesis k N
    ((radialIncidentCoordinates k N) ((radialIncidentCoordinates k N).symm c)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- No alternative choices of coordinates or fitted coefficients can change
this transfer while preserving its prescribed complete-source action. -/
theorem radialReturnTransfer_unique (k N : ℕ)
    (U : RadialIncidentSpan k N →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier)
    (hU : ∀ c : Fin N → ℂ, U (radialIncidentVector k N c) = radialReturnedSynthesis k N c) :
    U = radialReturnTransfer k N := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := (radialIncidentCoordinates k N).symm.surjective x
  exact (hU c).trans (radialReturnTransfer_exact k N c).symm

/-- Native quotient multiplication keeps the SAME finite feature span. -/
theorem radialReturnedSynthesis_eq_incident_multiply (k N : ℕ) (c : Fin N → ℂ) :
    radialReturnedSynthesis k N c = radialIncidentSynthesis k N
      (fun i => c i * completedNativeHermiteBiehlerChiralQuotient
        (canonicalCompletedC3RadialTiltPoint k i)) := by
  simp only [radialReturnedSynthesis, radialIncidentSynthesis, LinearMap.coe_mk,
    AddHom.coe_mk, completedNativeRadialChiralMultiplierState, smul_smul]

/-- The finite transfer returns to its source span, without enlarging the metric. -/
theorem radialReturnTransfer_mem_incidentSpan (k N : ℕ) (x : RadialIncidentSpan k N) :
    radialReturnTransfer k N x ∈ (radialIncidentSynthesis k N).range := by
  obtain ⟨c, rfl⟩ := (radialIncidentCoordinates k N).symm.surjective x
  change radialReturnTransfer k N (radialIncidentVector k N c) ∈ _
  rw [radialReturnTransfer_exact, radialReturnedSynthesis_eq_incident_multiply]
  exact ⟨_, rfl⟩

/-- Source-facing vector identity: the exact transfer takes the incident
combination of the SAME completed channels to their returned combination. -/
theorem radialReturnTransfer_source_pair (k N : ℕ) (c : Fin N → ℂ)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (radialIncidentVector k N c : CanonicalCompletedNativeChiralCauchyCarrier) =
        sourceCompanion k c 1 + Complex.I • sourceValue k c 1 ∧
      radialReturnTransfer k N (radialIncidentVector k N c) =
        sourceCompanion k c 1 - Complex.I • sourceValue k c 1 := by
  constructor
  · rw [radialIncidentVector_coe]
    simpa only [Complex.ofReal_one, one_pow, mul_one, radialIncidentSynthesis,
      LinearMap.coe_mk, AddHom.coe_mk] using incident_synthesis_eq_source k c 1 hpositive
  · rw [radialReturnTransfer_exact]
    simpa only [Complex.ofReal_one, one_pow, mul_one, radialReturnedSynthesis,
      LinearMap.coe_mk, AddHom.coe_mk] using returned_synthesis_eq_source k c 1 hpositive

/-- Full polarized source balance: arbitrary independent coefficient vectors
are synthesized before the two pairings, with every cross term retained. -/
theorem radialReturnTransfer_polarized_balance (k N : ℕ) (c d : Fin N → ℂ)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    inner ℂ (radialIncidentVector k N c : CanonicalCompletedNativeChiralCauchyCarrier)
        (radialIncidentVector k N d : CanonicalCompletedNativeChiralCauchyCarrier) -
      inner ℂ (radialReturnTransfer k N (radialIncidentVector k N c))
        (radialReturnTransfer k N (radialIncidentVector k N d)) =
      polarizedSourceBalance k c d 1 1 := by
  rw [(radialReturnTransfer_source_pair k N c hpositive).1,
    (radialReturnTransfer_source_pair k N d hpositive).1,
    (radialReturnTransfer_source_pair k N c hpositive).2,
    (radialReturnTransfer_source_pair k N d hpositive).2]
  rfl

/-- The exact integrated storage is the finite transfer's energy defect.
This is an identity, not a new sign premise. -/
theorem storage_one_eq_finiteTransfer_energy (k N : ℕ) (c : Fin N → ℂ) :
    (storage k c 1).re = ‖radialIncidentVector k N c‖ ^ 2 -
      ‖radialReturnTransfer k N (radialIncidentVector k N c)‖ ^ 2 := by
  rw [radialReturnTransfer_exact, radialIncidentVector_norm, storage_re_eq_norm_balance]
  simp only [Complex.ofReal_one, one_pow, mul_one, radialIncidentSynthesis,
    radialReturnedSynthesis, LinearMap.coe_mk, AddHom.coe_mk]

/-- Existence and finite-dimensional boundedness do not supply the remaining
constant ONE. This is the precise source-specific contractivity test. -/
theorem radialReturnTransfer_norm_le_one_iff_storage (k N : ℕ) :
    ‖radialReturnTransfer k N‖ ≤ 1 ↔ ∀ c : Fin N → ℂ, 0 ≤ (storage k c 1).re := by
  rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [one_mul]
  constructor
  · intro h c
    rw [storage_one_eq_finiteTransfer_energy]
    exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (h (radialIncidentVector k N c)))
  · intro h x
    obtain ⟨c, rfl⟩ := (radialIncidentCoordinates k N).symm.surjective x
    have hc := h c
    rw [storage_one_eq_finiteTransfer_energy] at hc
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sub_nonneg.mp hc)

/-- The SAME all-order quantifiers survive; no cutoff uniform in N is inserted. -/
theorem radialReturnTransfer_eventually_norm_le_one_iff_storage :
    (∀ N : ℕ, ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1) ↔
      ∀ N : ℕ, ∀ᶠ k : ℕ in atTop, ∀ c : Fin N → ℂ, 0 ≤ (storage k c 1).re := by
  constructor
  · intro h N
    filter_upwards [h N] with k hk
    exact (radialReturnTransfer_norm_le_one_iff_storage k N).mp hk
  · intro h N
    filter_upwards [h N] with k hk
    exact (radialReturnTransfer_norm_le_one_iff_storage k N).mpr hk

/-- Canaries at ANY finite order: the exact native action on each original
basis vector, including samples zero and one, uses no new readout. -/
theorem radialReturnTransfer_basis (k N : ℕ) (i : Fin N) :
    radialReturnTransfer k N (radialIncidentVector k N (Pi.single i 1)) =
      completedNativeHermiteBiehlerChiralQuotient
        (canonicalCompletedC3RadialTiltPoint k i) • completedNativeRadialChiralCauchyState k i := by
  classical
  rw [radialReturnTransfer_exact]
  simp [radialReturnedSynthesis, completedNativeRadialChiralMultiplierState]

/-- The operator norm gate is EXACTLY the old complete camera/Green
correction bound, not a new or weaker positivity assumption. -/
theorem radialReturnTransfer_norm_le_one_iff_cameraCorrection (k N : ℕ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    ‖radialReturnTransfer k N‖ ≤ 1 ↔ ∀ c : Fin N → ℂ,
      (coisometricFourChannelBalance k c c 1 1 (fun i => (hstrip i).1)).im ≤
        ‖coisometricSourceSynthesis k c 1 (fun i => (hstrip i).1)‖ ^ 2 := by
  rw [radialReturnTransfer_norm_le_one_iff_storage]
  exact forall_congr' fun c => storage_nonnegative_iff_coisometricCorrection_le_energy
    k c 1 hstrip hpositive

end
end CarrySelfAdjointOperator.ChiralReturn


import CarrySelfAdjointOperator.AtomicLogDerivativeResidue
import CarrySelfAdjointOperator.CompletedNativeJacobiCyclicAtomicExtraction

/-!
# Exact multiplicity of a completed native cyclic atom

The local order of the native characteristic fixes the coefficient of its
Weyl pole and hence the positive cyclic mass at the reciprocal-square
eigenvalue. The vectorial atomic construction remains the existing one.
-/

open Filter Topology

namespace CarrySelfAdjointOperator

noncomputable section

/-- The scaled height Weyl readout retains the analytic multiplicity,
with its normalization by twice the height. -/
theorem completedNativeJacobiWeylHeightContinuation_scaled_tendsto_multiplicity
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain) (hz₀ : z₀ ≠ 0) :
    Tendsto
      (fun z : ℂ => (z - z₀) * completedNativeJacobiWeylHeightContinuation z)
      (𝓝[≠] z₀)
      (𝓝 (-(analyticOrderNatAt completedNativeOperatorCharacteristic z₀ : ℂ) /
        (2 * z₀))) := by
  have hhalf := tendsto_mul_neg_half_logDeriv_eq_analyticOrderNatAt
    (completedNativeOperatorCharacteristic_analyticAt hzDomain)
    (completedNativeOperatorCharacteristic_analyticOrderAt_ne_top hzDomain)
  have hid : Tendsto (fun z : ℂ => z) (𝓝[≠] z₀) (𝓝 z₀) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hquot := hhalf.div hid hz₀
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] z₀, z ≠ 0 :=
    (continuousAt_id.eventually_ne hz₀).filter_mono nhdsWithin_le_nhds
  have heq :
      (fun z : ℂ => ((z - z₀) * (-logDeriv completedNativeOperatorCharacteristic z / 2)) / z)
        =ᶠ[𝓝[≠] z₀]
      (fun z : ℂ => (z - z₀) * completedNativeJacobiWeylHeightContinuation z) := by
    filter_upwards [hne] with z hz
    simp only [completedNativeJacobiWeylHeightContinuation, if_neg hz,
      completedNativeOperatorLogDerivative, logDeriv_apply]
    ring
  simpa only [div_div] using hquot.congr' heq

/-- The coefficient of a native height Weyl pole is the negative
analytic multiplicity divided by twice the height. -/
theorem completedNativeJacobiWeylHeightContinuation_trailingCoeff_eq_multiplicity
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    meromorphicTrailingCoeffAt completedNativeJacobiWeylHeightContinuation z₀ =
      -(analyticOrderNatAt completedNativeOperatorCharacteristic z₀ : ℂ) /
        (2 * z₀) := by
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  have hmeromorphic :=
    completedNativeJacobiWeylHeightContinuation_meromorphicAt hzDomain
  have horder :=
    (completedNativeJacobiWeylHeightContinuation_meromorphicOrderAt_eq_neg_one_iff_zero
      hzDomain).2 hzero
  have htrail := hmeromorphic.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [horder] at htrail
  have hpower : -((((-1 : ℤ) : WithTop ℤ).untop₀)) = (1 : ℤ) := by norm_num
  rw [hpower] at htrail
  simp only [zpow_one, smul_eq_mul] at htrail
  exact tendsto_nhds_unique htrail
    (completedNativeJacobiWeylHeightContinuation_scaled_tendsto_multiplicity
      hzDomain hz₀)

namespace CompletedNativeRealHPCarrierCertificate

/-- The reciprocal-square coordinate sends the native height pole to
minus the multiplicity times the Jacobi eigenvalue. -/
theorem positiveJacobiAtomicCyclicResidue_eq_multiplicity
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    positiveJacobiAtomicCyclicResidue z₀ =
      -(analyticOrderNatAt completedNativeOperatorCharacteristic z₀ : ℂ) / z₀ ^ 2 := by
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  rw [positiveJacobiAtomicCyclicResidue,
    completedNativeJacobiWeylHeightContinuation_trailingCoeff_eq_multiplicity hzDomain hzero]
  field_simp

/-- At a real native zero, the positive cyclic atomic mass is its
analytic multiplicity divided by the square of its height. -/
theorem positiveJacobiAtomicCyclicMass_eq_multiplicity
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hz₀Real : z₀.im = 0) :
    positiveJacobiAtomicCyclicMass z₀ =
      (analyticOrderNatAt completedNativeOperatorCharacteristic z₀ : ℝ) / z₀.re ^ 2 := by
  rw [positiveJacobiAtomicCyclicMass,
    positiveJacobiAtomicCyclicResidue_eq_multiplicity hzDomain hzero]
  have hz₀ : z₀ = (z₀.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hz₀Real
  rw [hz₀]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re, neg_div, neg_neg]

end CompletedNativeRealHPCarrierCertificate

end

end CarrySelfAdjointOperator

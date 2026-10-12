import CarrySelfAdjointOperator.NativeIntervalMultiplier
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! The geometric log u clock on its maximal domain in the original complex H.
The regularizer is the already constructed physical multiplier u. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open MeasureTheory
open scoped InnerProductSpace unitInterval ComplexConjugate
noncomputable section
set_option autoImplicit false

private def logWeighted (f : CanonicalCompletedNativeChiralCauchyCarrier)
    (u : unitInterval) : ℂ := (Real.log (u : ℝ) : ℂ)*f u

private theorem logWeighted_measurable (f : CanonicalCompletedNativeChiralCauchyCarrier) :
    AEStronglyMeasurable (logWeighted f) volume :=
  ((Real.measurable_log.comp measurable_subtype_coe).complex_ofReal.aestronglyMeasurable).mul
    (Lp.aestronglyMeasurable f)

/-- Precisely the maximal multiplication domain; membership is a genuine MemLp gate. -/
def geometricClockDomain : Submodule ℂ CanonicalCompletedNativeChiralCauchyCarrier where
  carrier := {f | MemLp (logWeighted f) 2 volume}
  zero_mem' := by
    apply (Lp.memLp (0 : CanonicalCompletedNativeChiralCauchyCarrier)).ae_eq
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure unitInterval)] with u hu
    change (0 : CanonicalCompletedNativeChiralCauchyCarrier) u =
      logWeighted (0 : CanonicalCompletedNativeChiralCauchyCarrier) u
    simp only [logWeighted, hu, Pi.zero_apply, mul_zero]
  add_mem' := by
    intro f g hf hg
    apply (hf.add hg).ae_eq
    filter_upwards [Lp.coeFn_add f g] with u hu
    change logWeighted f u + logWeighted g u = logWeighted (f+g) u
    simp only [logWeighted, hu, Pi.add_apply, mul_add]
  smul_mem' := by
    intro c f hf
    apply (hf.const_smul c).ae_eq
    filter_upwards [Lp.coeFn_smul c f] with u hu
    simp only [Pi.smul_apply, logWeighted, hu, smul_eq_mul]
    ring

private def geometricClockLinear : geometricClockDomain →ₗ[ℂ]
    CanonicalCompletedNativeChiralCauchyCarrier where
  toFun f := f.property.toLp (logWeighted f.val)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (f+g).property,
      Lp.coeFn_add f.val g.val, Lp.coeFn_add
        (f.property.toLp (logWeighted f.val)) (g.property.toLp (logWeighted g.val)),
      MemLp.coeFn_toLp f.property, MemLp.coeFn_toLp g.property] with u hfg ha hb hf hg
    change (f+g).property.toLp (logWeighted (f+g).val) u =
      (f.property.toLp (logWeighted f.val)+g.property.toLp (logWeighted g.val)) u
    rw [hfg, hb]
    simp only [logWeighted, Submodule.coe_add, ha, Pi.add_apply, hf, hg, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (c • f).property, Lp.coeFn_smul c f.val,
      Lp.coeFn_smul c (f.property.toLp (logWeighted f.val)),
      MemLp.coeFn_toLp f.property] with u hcf hc hcm hf
    change (c • f).property.toLp (logWeighted (c • f).val) u =
      (c • f.property.toLp (logWeighted f.val)) u
    rw [hcf, hcm]
    simp only [logWeighted, Submodule.coe_smul, hc, Pi.smul_apply, smul_eq_mul,
      hf]
    ring

/-- Unbounded complex linear multiplication by log u. -/
def geometricLogClock : CanonicalCompletedNativeChiralCauchyCarrier →ₗ.[ℂ]
    CanonicalCompletedNativeChiralCauchyCarrier where
  domain := geometricClockDomain
  toFun := geometricClockLinear

theorem geometricLogClock_ae (f : geometricLogClock.domain) :
    (geometricLogClock f : unitInterval → ℂ) =ᵐ[volume] logWeighted f.val :=
  f.property.coeFn_toLp

/-- The bounded product u log u extends continuously through the zero endpoint. -/
def geometricClockTransferCoefficient : C(unitInterval, ℂ) where
  toFun u := (((u : ℝ)*Real.log (u : ℝ) : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Real.continuous_mul_log.comp continuous_subtype_val)

def geometricClockTransfer := intervalMultiplier geometricClockTransferCoefficient

theorem physicalRadialAdvance_mem_geometricClockDomain
    (f : CanonicalCompletedNativeChiralCauchyCarrier) :
    physicalRadialAdvance f ∈ geometricClockDomain := by
  apply (Lp.memLp (geometricClockTransfer f)).ae_eq
  filter_upwards [intervalMultiplier_ae geometricClockTransferCoefficient f,
    intervalMultiplier_ae physicalRadialCoefficient f] with u hB hA
  change intervalMultiplier geometricClockTransferCoefficient f u = logWeighted (physicalRadialAdvance f) u
  rw [hB]
  change geometricClockTransferCoefficient u * f u =
    (Real.log (u : ℝ) : ℂ) * intervalMultiplier physicalRadialCoefficient f u
  rw [hA]
  simp only [geometricClockTransferCoefficient, physicalRadialCoefficient,
    ContinuousMap.coe_mk, Complex.ofReal_mul]
  ring

private def radialIntoClockDomain : CanonicalCompletedNativeChiralCauchyCarrier →ₗ[ℂ]
    geometricLogClock.domain :=
  physicalRadialAdvance.toLinearMap.codRestrict geometricLogClock.domain
    physicalRadialAdvance_mem_geometricClockDomain

private theorem clock_radial_transfer (f : CanonicalCompletedNativeChiralCauchyCarrier) :
    geometricLogClock (radialIntoClockDomain f) = geometricClockTransfer f := by
  apply Lp.ext
  filter_upwards [geometricLogClock_ae (radialIntoClockDomain f),
    intervalMultiplier_ae physicalRadialCoefficient f,
    intervalMultiplier_ae geometricClockTransferCoefficient f] with u hT hA hB
  rw [hT]
  change logWeighted (physicalRadialAdvance f) u =
    intervalMultiplier geometricClockTransferCoefficient f u
  rw [hB]
  change (Real.log (u : ℝ) : ℂ) * intervalMultiplier physicalRadialCoefficient f u =
    geometricClockTransferCoefficient u * f u
  rw [hA]
  simp only [geometricClockTransferCoefficient, physicalRadialCoefficient,
    ContinuousMap.coe_mk, Complex.ofReal_mul]
  ring

private theorem interval_coordinate_ae_ne_zero :
    ∀ᵐ u : unitInterval, ((u : ℝ) : ℂ) ≠ 0 := by
  filter_upwards [show ∀ᵐ u : unitInterval, u ≠ 0 by rw [ae_iff]; simp] with u hu
  intro h
  apply hu
  apply Subtype.ext
  exact_mod_cast h

/-- The radial regularizer is injective on the original H. -/
theorem physicalRadialAdvance_injective : Function.Injective physicalRadialAdvance := by
  intro f g hfg
  apply Lp.ext
  have he : (physicalRadialAdvance f : unitInterval → ℂ) =ᵐ[volume] physicalRadialAdvance g := by rw [hfg]
  filter_upwards [intervalMultiplier_ae physicalRadialCoefficient f,
    intervalMultiplier_ae physicalRadialCoefficient g, he, interval_coordinate_ae_ne_zero]
    with u hf hg heq hu
  apply mul_left_cancel₀ hu
  exact hf.symm.trans (heq.trans hg)

/-- Dense maximal domain, without any Laguerre completeness assumption. -/
theorem geometricClockDomain_dense :
    Dense (geometricClockDomain : Set CanonicalCompletedNativeChiralCauchyCarrier) := by
  have hd : Dense (physicalRadialAdvance.toLinearMap.range :
      Set CanonicalCompletedNativeChiralCauchyCarrier) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      ← physicalRadialAdvance.toLinearMap.range.orthogonal_orthogonal_eq_closure,
      physicalRadialAdvance_isSelfAdjoint.isSymmetric.orthogonal_range,
      LinearMap.ker_eq_bot.mpr physicalRadialAdvance_injective,
      Submodule.bot_orthogonal_eq_top]
  apply hd.mono
  rintro f ⟨g, rfl⟩
  exact physicalRadialAdvance_mem_geometricClockDomain g

/-- Symmetry holds on the maximal domain, in the complex inner product convention. -/
theorem geometricLogClock_isFormalAdjoint : geometricLogClock.IsFormalAdjoint geometricLogClock := by
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [geometricLogClock_ae f, geometricLogClock_ae g] with u hf hg
  change inner ℂ (geometricLogClock f u) (g.val u) =
    inner ℂ (f.val u) (geometricLogClock g u)
  rw [hf, hg]
  simp only [logWeighted, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

private theorem geometricClockTransfer_isSelfAdjoint : IsSelfAdjoint geometricClockTransfer := by
  apply intervalMultiplier_isSelfAdjoint
  intro u
  simp [geometricClockTransferCoefficient]

private theorem geometricLogClock_adjoint_ae (g : geometricLogClock.adjoint.domain) :
    logWeighted g.val =ᵐ[volume] (geometricLogClock.adjoint g : unitInterval → ℂ) := by
  let h := geometricLogClock.adjoint g
  have he : geometricClockTransfer g.val = physicalRadialAdvance h := by
    apply ext_inner_right ℂ
    intro k
    have hf := (LinearPMap.adjoint_isFormalAdjoint geometricClockDomain_dense) g
      (radialIntoClockDomain k)
    change inner ℂ h (physicalRadialAdvance k) =
      inner ℂ g.val (geometricLogClock (radialIntoClockDomain k)) at hf
    rw [clock_radial_transfer] at hf
    calc
      _ = inner ℂ g.val (geometricClockTransfer k) :=
        geometricClockTransfer_isSelfAdjoint.isSymmetric g.val k
      _ = inner ℂ h (physicalRadialAdvance k) := hf.symm
      _ = _ := (physicalRadialAdvance_isSelfAdjoint.isSymmetric h k).symm
  have heae : (geometricClockTransfer g.val : unitInterval → ℂ) =ᵐ[volume]
      physicalRadialAdvance h := by rw [he]
  filter_upwards [intervalMultiplier_ae geometricClockTransferCoefficient g.val,
    intervalMultiplier_ae physicalRadialCoefficient h, heae,
    interval_coordinate_ae_ne_zero] with u hB hA hu hzero
  change logWeighted g.val u = h u
  apply mul_left_cancel₀ hzero
  have hp := hB.symm.trans (hu.trans hA)
  simp only [geometricClockTransferCoefficient, physicalRadialCoefficient,
    ContinuousMap.coe_mk, Complex.ofReal_mul] at hp
  dsimp [logWeighted]
  simpa only [mul_assoc] using hp

private theorem geometricLogClock_adjoint_domain_le :
    geometricLogClock.adjoint.domain ≤ geometricLogClock.domain := by
  intro g hg
  let gAdj : geometricLogClock.adjoint.domain := ⟨g, hg⟩
  exact (Lp.memLp (geometricLogClock.adjoint gAdj)).ae_eq
    (geometricLogClock_adjoint_ae gAdj).symm

private theorem geometricLogClock_adjoint_le : geometricLogClock.adjoint ≤ geometricLogClock := by
  refine ⟨geometricLogClock_adjoint_domain_le, ?_⟩
  intro g f hgf
  apply Lp.ext
  have he : (g.val : unitInterval → ℂ) =ᵐ[volume] f.val := by rw [hgf]
  filter_upwards [geometricLogClock_adjoint_ae g, geometricLogClock_ae f, he]
    with u hg hf hu
  exact hg.symm.trans ((congrArg (fun z => (Real.log (u : ℝ) : ℂ)*z) hu).trans hf.symm)

/-- The complex Hilbert adjoint has exactly the maximal original multiplication domain. -/
theorem geometricLogClock_adjoint_eq : geometricLogClock.adjoint = geometricLogClock :=
  le_antisymm geometricLogClock_adjoint_le
    (geometricLogClock_isFormalAdjoint.le_adjoint geometricClockDomain_dense)

/-- Independent self-adjointness proof on the original H; no Laguerre inverse is used. -/
theorem geometricLogClock_isSelfAdjoint : IsSelfAdjoint geometricLogClock := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact geometricLogClock_adjoint_eq

theorem geometricLogClock_isClosed : geometricLogClock.IsClosed :=
  geometricLogClock_isSelfAdjoint.isClosed


/-- Every logarithmic monomial is in the maximal geometric domain. -/
theorem logarithmicMonomialLp_mem_geometricClockDomain (n : ℕ) :
    logarithmicMonomialLp n ∈ geometricClockDomain := by
  apply (((memLp_interval_log_power (n+1)).ofReal (K := ℂ)).neg).ae_eq
  filter_upwards [logarithmicMonomialLp_ae n] with u hu
  change -((((-Real.log (u : ℝ))^(n+1) : ℝ) : ℂ)) = logWeighted (logarithmicMonomialLp n) u
  rw [logWeighted, hu]
  push_cast
  rw [pow_succ]
  ring

/-- All Laguerre modes lie in the same maximal domain, whether or not complete. -/
theorem laguerreMode_mem_geometricClockDomain (r : ℕ) : laguerreMode r ∈ geometricClockDomain := by
  unfold laguerreMode
  exact Submodule.sum_mem geometricClockDomain (fun a _ =>
    Submodule.smul_mem geometricClockDomain _ (logarithmicMonomialLp_mem_geometricClockDomain a))

/-- Explicit action on the logarithmic core. -/
theorem geometricLogClock_logarithmicMonomial (n : ℕ) :
    geometricLogClock ⟨logarithmicMonomialLp n, logarithmicMonomialLp_mem_geometricClockDomain n⟩ =
      -logarithmicMonomialLp (n+1) := by
  apply Lp.ext
  filter_upwards [geometricLogClock_ae
      ⟨logarithmicMonomialLp n, logarithmicMonomialLp_mem_geometricClockDomain n⟩,
    logarithmicMonomialLp_ae n, logarithmicMonomialLp_ae (n+1),
    Lp.coeFn_neg (logarithmicMonomialLp (n+1))] with u hT hn hnext hneg
  rw [hT, hneg]
  simp only [logWeighted, hn, Pi.neg_apply, hnext, Complex.ofReal_pow, Complex.ofReal_neg]
  rw [pow_succ]
  ring

/-- A whole-core moment expansion, preceding any Jacobi truncation. -/
theorem geometricLogClock_laguerre_expansion (r : ℕ) :
    geometricLogClock ⟨laguerreMode r, laguerreMode_mem_geometricClockDomain r⟩ =
      ∑ a ∈ Finset.range (r+1),
        -(((((-1 : ℝ)^a * (r.choose a : ℝ) / (a.factorial : ℝ)) : ℝ) : ℂ)) •
          logarithmicMonomialLp (a+1) := by
  let c : ℕ → ℂ := fun a => ((((-1 : ℝ)^a * (r.choose a : ℝ) / (a.factorial : ℝ)) : ℝ) : ℂ)
  apply Lp.ext
  filter_upwards [geometricLogClock_ae ⟨laguerreMode r, laguerreMode_mem_geometricClockDomain r⟩,
    laguerreMode_ae r, Lp.coeFn_finsetSum (Finset.range (r+1))
      (fun a => -(c a) • logarithmicMonomialLp (a+1)),
    (ae_all_iff).mpr (fun a => Lp.coeFn_smul (-(c a)) (logarithmicMonomialLp (a+1))),
    (ae_all_iff).mpr logarithmicMonomialLp_ae] with u hT hr hs hsmul hlog
  change geometricLogClock ⟨laguerreMode r, laguerreMode_mem_geometricClockDomain r⟩ u =
    (∑ a ∈ Finset.range (r+1), -(c a) • logarithmicMonomialLp (a+1) :
      CanonicalCompletedNativeChiralCauchyCarrier) u
  rw [hT]
  change (Real.log (u : ℝ) : ℂ) * laguerreMode r u = _
  rw [hr, hs]
  simp only [Finset.mul_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [hsmul a]
  simp only [Pi.smul_apply, smul_eq_mul, hlog (a+1), c,
    Complex.ofReal_pow, Complex.ofReal_neg, pow_succ]
  push_cast
  ring

/-- The first three rows of the genuine geometric Jacobi action. -/
theorem geometricLogClock_first_three_Jacobi (r : Fin 3) :
    geometricLogClock ⟨laguerreMode r.val, laguerreMode_mem_geometricClockDomain r.val⟩ =
      ((r.val+1 : ℕ) : ℂ) • laguerreMode (r.val+1) -
      ((2*r.val+1 : ℕ) : ℂ) • laguerreMode r.val + (r.val : ℂ) • laguerreMode (r.val-1) := by
  rw [geometricLogClock_laguerre_expansion]
  fin_cases r <;>
    norm_num [laguerreMode, Finset.sum_range_succ, Nat.choose] <;> module

/-- Pointwise spectral canary only: exp(log u)=u away from the null endpoint. -/
theorem geometricClock_exp_canary :
    (fun u : unitInterval => Real.exp (Real.log (u : ℝ))) =ᵐ[volume] (fun u => (u : ℝ)) := by
  filter_upwards [interval_coordinate_ae_ne_zero] with u hu
  apply Real.exp_log
  have hn : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  exact lt_of_le_of_ne u.property.1 (Ne.symm hn)


/-- Every original half-density address lies in the geometric clock domain. -/
theorem completedNativeChiralCauchyFeature_mem_geometricClockDomain (j : ℕ) :
    completedNativeChiralCauchyFeature j ∈ geometricClockDomain := by
  have hlog : MemLp (fun u : unitInterval => (Real.log (u : ℝ) : ℂ)) 2 volume := by
    apply (((memLp_interval_log_power 1).ofReal (K := ℂ)).neg).ae_eq
    filter_upwards with u
    simp
  apply hlog.of_le_mul (c := 1) (logWeighted_measurable _)
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
    (completedNativeChiralCauchyContinuousFeature j)] with u hj
  change ‖(Real.log (u : ℝ) : ℂ)*completedNativeChiralCauchyFeature j u‖ ≤
    1*‖(Real.log (u : ℝ) : ℂ)‖
  have hφ : ‖completedNativeChiralCauchyFeature j u‖ ≤ 1 := by
    change ‖ContinuousMap.toLp 2 volume ℂ (completedNativeChiralCauchyContinuousFeature j) u‖ ≤ 1
    rw [hj]
    simp only [completedNativeChiralCauchyContinuousFeature, ContinuousMap.coe_mk,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg u.property.1 _))]
    have hs : Real.sqrt (u : ℝ) ≤ 1 := by simpa using Real.sqrt_le_sqrt u.property.2
    have hp : (u : ℝ)^j ≤ 1 := pow_le_one₀ u.property.1 u.property.2
    exact (mul_le_mul hs hp (pow_nonneg u.property.1 _) (by norm_num)).trans (by norm_num)
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left hφ (norm_nonneg (Real.log (u : ℝ) : ℂ))

/-- Native amplitude remains part of the same domain; no normalized replacement is made. -/
theorem completedNativeRadialChiralCauchyState_mem_geometricClockDomain (k j : ℕ) :
    completedNativeRadialChiralCauchyState k j ∈ geometricClockDomain := by
  exact geometricClockDomain.smul_mem _
    (completedNativeChiralCauchyFeature_mem_geometricClockDomain j)


/-- The literal Weyl coordinate retains both its additive one and its scale shift. -/
theorem weyl_literal_log_coordinate_shift (ell : ℝ) (hell : 0 < ell) :
    (fun u : unitInterval => 1+Real.log (ell*(u : ℝ))) =ᵐ[volume]
      (fun u => (1+Real.log ell)+Real.log (u : ℝ)) := by
  filter_upwards [interval_coordinate_ae_ne_zero] with u hu
  have hn : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  rw [Real.log_mul hell.ne' hn]
  ring

end
end CarrySelfAdjointOperator.NativeLaguerre

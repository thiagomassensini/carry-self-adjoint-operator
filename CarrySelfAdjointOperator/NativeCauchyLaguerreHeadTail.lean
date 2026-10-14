import CarrySelfAdjointOperator.NativeCauchyLaguerreShift
import CarrySelfAdjointOperator.NativePhysicalLaguerreObservability
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate lp
open Filter Topology CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem laguerreHead_inner (R : ℕ) (x y : ℓ²(ℕ, ℂ)) :
    inner ℂ (laguerreHead R x) (laguerreHead R y) =
      ∑ r ∈ Finset.range (R+1), inner ℂ (x r) (y r) := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := Finset.range (R+1)) (fun r hr => by
    have h : ¬r ≤ R := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
    simp [laguerreHead_apply, h])]
  apply Finset.sum_congr rfl
  intro r hr
  have h : r ≤ R := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
  simp [h]

/-- Polarized head plus PHYSICAL vector tail, for independent infinite inputs. -/
theorem physicalCauchy_head_tail_inner (R : ℕ) (x y : PhysicalCauchySpace) :
    inner ℂ x y =
      inner ℂ (laguerreHead R (cauchyLaguerreIsometry x))
        (laguerreHead R (cauchyLaguerreIsometry y)) +
      inner ℂ (physicalCauchyShift (R+1) x) (physicalCauchyShift (R+1) y) := by
  rw [← cauchyLaguerreIsometry.inner_map_map x y,
    ← cauchyLaguerreIsometry.inner_map_map (physicalCauchyShift (R+1) x)
      (physicalCauchyShift (R+1) y),
    physicalCauchyShift_intertwines, physicalCauchyShift_intertwines,
    laguerreHead_inner, lp.inner_eq_tsum, lp.inner_eq_tsum]
  have h := ((lp.summable_inner (𝕜 := ℂ) (cauchyLaguerreIsometry x)
    (cauchyLaguerreIsometry y)).sum_add_tsum_nat_add (R+1)).symm
  simpa only [carryVerticalL2BackwardShift_apply] using h

abbrev PhysicalHeadTailSpace := WithLp 2 (ℓ²(ℕ, ℂ) × PhysicalCauchySpace)

/-- A Hilbert lift whose second component remains a vector in the physical closure. -/
def physicalHeadTailLinear (R : ℕ) : PhysicalCauchySpace →ₗ[ℂ] PhysicalHeadTailSpace where
  toFun x := WithLp.toLp 2
    (laguerreHead R (cauchyLaguerreIsometry x), physicalCauchyShift (R+1) x)
  map_add' x y := by
    apply WithLp.ofLp_injective
    simp only [WithLp.ofLp_add, map_add]
    rfl
  map_smul' a x := by
    apply WithLp.ofLp_injective
    simp only [WithLp.ofLp_smul, map_smul]
    rfl

theorem physicalHeadTailLinear_inner (R : ℕ) (x y : PhysicalCauchySpace) :
    inner ℂ (physicalHeadTailLinear R x) (physicalHeadTailLinear R y) = inner ℂ x y :=
  (physicalCauchy_head_tail_inner R x y).symm

def physicalHeadTailIsometry (R : ℕ) : PhysicalCauchySpace →ₗᵢ[ℂ] PhysicalHeadTailSpace :=
  { physicalHeadTailLinear R with
    norm_map' := fun x => by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
        physicalHeadTailLinear_inner] }

theorem physicalCauchy_head_tail_energy (R : ℕ) (x : PhysicalCauchySpace) :
    ‖laguerreHead R (cauchyLaguerreIsometry x)‖ ^ 2 +
      ‖physicalCauchyShift (R+1) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := congrArg Complex.re (physicalCauchy_head_tail_inner R x x)
  simp only [Complex.add_re] at h
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact h.symm

theorem laguerreHead_refines {R T : ℕ} (hRT : R ≤ T) (x : ℓ²(ℕ, ℂ)) :
    laguerreHead R (laguerreHead T x) = laguerreHead R x := by
  ext r
  by_cases hr : r ≤ R
  · simp [hr, hr.trans hRT]
  · simp [hr]

/-- Refinement retains the old head and evolves its PHYSICAL tail by the same semigroup. -/
theorem physicalHeadTail_refinement {R T : ℕ} (hRT : R ≤ T) (x : PhysicalCauchySpace) :
    laguerreHead R (physicalHeadTailIsometry T x).fst =
      (physicalHeadTailIsometry R x).fst ∧
    physicalCauchyShift (T-R) (physicalHeadTailIsometry R x).snd =
      (physicalHeadTailIsometry T x).snd := by
  constructor
  · exact laguerreHead_refines hRT _
  · change physicalCauchyShift (T-R) (physicalCauchyShift (R+1) x) =
      physicalCauchyShift (T+1) x
    rw [← ContinuousLinearMap.comp_apply, ← physicalCauchyShift_add]
    have he : T-R+(R+1) = T+1 := by omega
    rw [he]

/-- Finite synthesis in the closure, retaining the original half densities. -/
def physicalFiniteSynthesis (m : ℕ) : (Fin m → ℂ) →ₗ[ℂ] PhysicalCauchySpace where
  toFun c := ∑ j, c j • physicalCauchyFeature j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

theorem physicalFiniteSynthesis_coe (m : ℕ) (c : Fin m → ℂ) :
    (physicalFiniteSynthesis m c : CanonicalCompletedNativeChiralCauchyCarrier) =
      ChiralReturn.radialIncidentSynthesis 0 m c := by
  simp [physicalFiniteSynthesis, ChiralReturn.radialIncidentSynthesis,
    completedNativeRadialChiralCauchyState]

theorem physicalFiniteSynthesis_injective (m : ℕ) :
    Function.Injective (physicalFiniteSynthesis m) := by
  intro c d h
  apply ChiralReturn.radialIncidentSynthesis_injective 0 m
  simpa only [physicalFiniteSynthesis_coe] using
    congrArg (fun x : PhysicalCauchySpace => (x : CanonicalCompletedNativeChiralCauchyCarrier)) h

def physicalFiniteHead (m R : ℕ) : (Fin m → ℂ) →ₗ[ℂ] (Fin (R+1) → ℂ) where
  toFun c r := cauchyLaguerreIsometry (physicalFiniteSynthesis m c) r.val
  map_add' c d := by funext r; simp
  map_smul' a c := by funext r; simp

/-- Every head shorter than the physical dimension misses a nonzero vector with full tail energy. -/
theorem shortHead_full_physical_tail (m R : ℕ) (hm : R+1 < m) :
    ∃ c : Fin m → ℂ, c ≠ 0 ∧ physicalFiniteSynthesis m c ≠ 0 ∧
      laguerreHead R (cauchyLaguerreIsometry (physicalFiniteSynthesis m c)) = 0 ∧
      ‖physicalCauchyShift (R+1) (physicalFiniteSynthesis m c)‖ =
        ‖physicalFiniteSynthesis m c‖ := by
  have hnon : ¬Function.Injective (physicalFiniteHead m R) := by
    intro hi
    have h := LinearMap.finrank_le_finrank_of_injective hi
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega
  have hk : ¬∀ c, physicalFiniteHead m R c = 0 → c = 0 := by
    intro h
    apply hnon
    exact LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr h)
  push Not at hk
  obtain ⟨c, hc, hcz⟩ := hk
  have hhead : laguerreHead R (cauchyLaguerreIsometry (physicalFiniteSynthesis m c)) = 0 := by
    ext r
    by_cases hr : r ≤ R
    · have he := congrFun hc (⟨r, by omega⟩ : Fin (R+1))
      simpa only [physicalFiniteHead, LinearMap.coe_mk, AddHom.coe_mk,
        laguerreHead_apply, if_pos hr, Pi.zero_apply, lp.coeFn_zero] using he
    · simp [hr]
  refine ⟨c, hcz, ?_, hhead, ?_⟩
  · intro hz
    apply hcz
    exact (physicalFiniteSynthesis_injective m) (by simpa using hz)
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [hhead, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] using
      physicalCauchy_head_tail_energy R (physicalFiniteSynthesis m c)

/-- Strong tail stability is not an operator norm limit: every physical tail has norm one. -/
theorem physicalCauchyShift_tail_opNorm_eq_one (R : ℕ) :
    ‖physicalCauchyShift (R+1)‖ = 1 := by
  obtain ⟨c, _, hc, _, ht⟩ := shortHead_full_physical_tail (R+2) R (by omega)
  apply le_antisymm (physicalCauchyShift_opNorm_le_one (R+1))
  have hn : 0 < ‖physicalFiniteSynthesis (R+2) c‖ := norm_pos_iff.mpr hc
  have h := (physicalCauchyShift (R+1)).le_opNorm (physicalFiniteSynthesis (R+2) c)
  rw [ht] at h
  nlinarith

end
end CarrySelfAdjointOperator.NativeLaguerre

import CarrySelfAdjointOperator.RealLinearPMapAdjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Two real Hilbert quadratures, before choosing complex scalars. The metric
is the existing product L2 metric. The partial-operator domain is doubled as
well; no complex structure on the original operator carrier is assumed. -/
namespace CarrySelfAdjointOperator.RealQuadrature
open scoped InnerProductSpace RealInnerProductSpace
noncomputable section
set_option autoImplicit false

abbrev Space (E : Type*) := WithLp 2 (E × E)

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Real quarter-turn on the two retained quadratures. -/
def J : Space E →ₗ[ℝ] Space E where
  toFun x := WithLp.toLp 2 (-x.snd, x.fst)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change -(x.snd + y.snd) = -x.snd + -y.snd
      abel
    · rfl
  map_smul' a x := by apply WithLp.ofLp_injective 2; ext <;> simp

@[simp] theorem J_fst (x : Space E) : (J x).fst = -x.snd := rfl
@[simp] theorem J_snd (x : Space E) : (J x).snd = x.fst := rfl

theorem J_squared (x : Space E) : J (J x) = -x := by
  apply WithLp.ofLp_injective 2
  ext <;> simp

theorem J_inner (x y : Space E) : inner ℝ (J x) (J y) = inner ℝ x y := by
  change inner ℝ (-x.snd) (-y.snd) + inner ℝ x.fst y.fst =
    inner ℝ x.fst y.fst + inner ℝ x.snd y.snd
  rw [inner_neg_neg]
  ring

theorem J_skew (x y : Space E) : inner ℝ (J x) y = -inner ℝ x (J y) := by
  change inner ℝ (-x.snd) y.fst + inner ℝ x.fst y.snd =
    -(inner ℝ x.fst (-y.snd) + inner ℝ x.snd y.fst)
  rw [inner_neg_left, inner_neg_right]
  ring

theorem J_norm (x : Space E) : ‖J x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, J_inner]

/-- Coordinatewise lifting of an existing real linear map. -/
def lift (T : E →ₗ[ℝ] F) : Space E →ₗ[ℝ] Space F where
  toFun x := WithLp.toLp 2 (T x.fst, T x.snd)
  map_add' x y := by apply WithLp.ofLp_injective 2; ext <;> simp
  map_smul' a x := by apply WithLp.ofLp_injective 2; ext <;> simp

@[simp] theorem lift_fst (T : E →ₗ[ℝ] F) (x : Space E) :
    (lift T x).fst = T x.fst := rfl
@[simp] theorem lift_snd (T : E →ₗ[ℝ] F) (x : Space E) :
    (lift T x).snd = T x.snd := rfl

theorem lift_J (T : E →ₗ[ℝ] F) (x : Space E) : lift T (J x) = J (lift T x) := by
  apply WithLp.ofLp_injective 2
  ext <;> simp

/-- A real isometry transports both the metric and its rotation-associated form. -/
theorem lift_isometry_pairings (T : E →ₗᵢ[ℝ] F) (x y : Space E) :
    inner ℝ (lift T.toLinearMap x) (lift T.toLinearMap y) = inner ℝ x y ∧
      inner ℝ (J (lift T.toLinearMap x)) (lift T.toLinearMap y) = inner ℝ (J x) y := by
  have hmetric (u v : Space E) :
      inner ℝ (lift T.toLinearMap u) (lift T.toLinearMap v) = inner ℝ u v := by
    change inner ℝ (T u.fst) (T v.fst) + inner ℝ (T u.snd) (T v.snd) =
      inner ℝ u.fst v.fst + inner ℝ u.snd v.snd
    rw [T.inner_map_map, T.inner_map_map]
  exact ⟨hmetric x y, by rw [← lift_J]; exact hmetric (J x) y⟩

/-- Exact natural domain of the doubled REAL partial operator. -/
def doubleDomain (T : E →ₗ.[ℝ] F) : Submodule ℝ (Space E) where
  carrier := {x | x.fst ∈ T.domain ∧ x.snd ∈ T.domain}
  zero_mem' := by simp
  add_mem' hx hy := ⟨T.domain.add_mem hx.1 hy.1, T.domain.add_mem hx.2 hy.2⟩
  smul_mem' a x hx := ⟨T.domain.smul_mem a hx.1, T.domain.smul_mem a hx.2⟩

theorem J_mem_doubleDomain_iff (T : E →ₗ.[ℝ] F) (x : Space E) :
    J x ∈ doubleDomain T ↔ x ∈ doubleDomain T := by
  change (-x.snd ∈ T.domain ∧ x.fst ∈ T.domain) ↔
    (x.fst ∈ T.domain ∧ x.snd ∈ T.domain)
  simp only [Submodule.neg_mem_iff, and_comm]

def doubleDomainFst (T : E →ₗ.[ℝ] F) (x : doubleDomain T) : T.domain :=
  ⟨(x : Space E).fst, x.property.1⟩
def doubleDomainSnd (T : E →ₗ.[ℝ] F) (x : doubleDomain T) : T.domain :=
  ⟨(x : Space E).snd, x.property.2⟩

/-- The operator is doubled before any complex scalar multiplication is chosen. -/
def double (T : E →ₗ.[ℝ] F) : Space E →ₗ.[ℝ] Space F where
  domain := doubleDomain T
  toFun :=
    { toFun := fun x => WithLp.toLp 2 (T (doubleDomainFst T x), T (doubleDomainSnd T x))
      map_add' x y := by
        apply WithLp.ofLp_injective 2
        have hf : doubleDomainFst T (x + y) = doubleDomainFst T x + doubleDomainFst T y := rfl
        have hs : doubleDomainSnd T (x + y) = doubleDomainSnd T x + doubleDomainSnd T y := rfl
        ext <;> simp only [hf, hs, T.map_add] <;> rfl
      map_smul' a x := by
        apply WithLp.ofLp_injective 2
        have hf : doubleDomainFst T (a • x) = a • doubleDomainFst T x := rfl
        have hs : doubleDomainSnd T (a • x) = a • doubleDomainSnd T x := rfl
        ext <;> simp only [hf, hs, T.map_smul] <;> rfl }

def domainJ (T : E →ₗ.[ℝ] F) (x : (double T).domain) : (double T).domain :=
  ⟨J (x : Space E), (J_mem_doubleDomain_iff T x).2 x.property⟩

/-- Domain-sensitive rotation commutation for an arbitrary unbounded real T. -/
theorem double_domainJ (T : E →ₗ.[ℝ] F) (x : (double T).domain) :
    double T (domainJ T x) = J (double T x) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change T ⟨-(x : Space E).snd, _⟩ = -T (doubleDomainSnd T x)
    have he : (⟨-(x : Space E).snd, _⟩ : T.domain) = -doubleDomainSnd T x := rfl
    rw [he, T.map_neg]
  · rfl

/-- Real formal-adjoint compatibility on the TWO natural domains. -/
theorem double_realAdjoint_pairing (T : E →ₗ.[ℝ] F)
    (hT : Dense (T.domain : Set E))
    (x : (double T).domain) (y : (double (T.realAdjoint hT)).domain) :
    inner ℝ (double T x) (y : Space F) =
      inner ℝ (x : Space E) (double (T.realAdjoint hT) y) := by
  change inner ℝ (T (doubleDomainFst T x)) (y : Space F).fst +
      inner ℝ (T (doubleDomainSnd T x)) (y : Space F).snd =
    inner ℝ (x : Space E).fst (T.realAdjoint hT (doubleDomainFst (T.realAdjoint hT) y)) +
      inner ℝ (x : Space E).snd (T.realAdjoint hT (doubleDomainSnd (T.realAdjoint hT) y))
  exact congrArg₂ (fun a b : ℝ => a + b)
    (T.realAdjoint_isFormalAdjoint hT (doubleDomainFst T x)
      (doubleDomainFst (T.realAdjoint hT) y))
    (T.realAdjoint_isFormalAdjoint hT (doubleDomainSnd T x)
      (doubleDomainSnd (T.realAdjoint hT) y))

end
end CarrySelfAdjointOperator.RealQuadrature

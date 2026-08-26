import CarrySelfAdjointOperator.RealLinearPMapReciprocalBlock
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Complexification of maximal real self-adjoint partial operators

A real Hilbert space `E` is complexified as the `L²` product `E × E`, with
`(x, y)` representing `x + i y`.  A real partial operator is extended on the
product of its two domains and acts coordinatewise.  This file keeps the
domain visible and proves the adjoint identity at the level of partial
operators.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- The canonical Hilbert complexification of a real Hilbert space. -/
def RealHilbertComplexification (E : Type*) := WithLp 2 (E × E)

namespace RealHilbertComplexification

variable {E : Type*}

instance [NormedAddCommGroup E] : NormedAddCommGroup
    (RealHilbertComplexification E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

instance [NormedAddCommGroup E] [CompleteSpace E] : CompleteSpace
    (RealHilbertComplexification E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

/-- Real coordinate of a complexified vector. -/
def re [NormedAddCommGroup E] (x : RealHilbertComplexification E) : E :=
  (WithLp.ofLp x).1

/-- Imaginary coordinate of a complexified vector. -/
def im [NormedAddCommGroup E] (x : RealHilbertComplexification E) : E :=
  (WithLp.ofLp x).2

/-- Package two real vectors as one vector in the complexification. -/
def mk [NormedAddCommGroup E] (x y : E) : RealHilbertComplexification E :=
  WithLp.toLp 2 (x, y)

@[simp] theorem re_mk [NormedAddCommGroup E] (x y : E) :
    re (mk x y) = x := rfl

@[simp] theorem im_mk [NormedAddCommGroup E] (x y : E) :
    im (mk x y) = y := rfl

@[simp] theorem re_zero [NormedAddCommGroup E] :
    re (0 : RealHilbertComplexification E) = 0 := rfl

@[simp] theorem im_zero [NormedAddCommGroup E] :
    im (0 : RealHilbertComplexification E) = 0 := rfl

@[simp] theorem re_add [NormedAddCommGroup E]
    (x y : RealHilbertComplexification E) :
    re (x + y) = re x + re y := rfl

@[simp] theorem im_add [NormedAddCommGroup E]
    (x y : RealHilbertComplexification E) :
    im (x + y) = im x + im y := rfl

@[simp] theorem re_neg [NormedAddCommGroup E]
    (x : RealHilbertComplexification E) :
    re (-x) = -re x := rfl

@[simp] theorem im_neg [NormedAddCommGroup E]
    (x : RealHilbertComplexification E) :
    im (-x) = -im x := rfl

@[ext] theorem ext [NormedAddCommGroup E]
    {x y : RealHilbertComplexification E}
    (hre : re x = re y) (him : im x = im y) : x = y := by
  apply WithLp.ofLp_injective 2
  exact Prod.ext hre him

/-- Canonical complex scalar multiplication on two real quadratures. -/
def complexSMul [NormedAddCommGroup E] [Module ℝ E]
    (z : ℂ) (x : RealHilbertComplexification E) :
    RealHilbertComplexification E :=
  mk (z.re • re x - z.im • im x)
    (z.im • re x + z.re • im x)

@[reducible] instance [NormedAddCommGroup E] [Module ℝ E] :
    SMul ℂ (RealHilbertComplexification E) :=
  ⟨complexSMul⟩

@[simp] theorem re_smul [NormedAddCommGroup E] [Module ℝ E]
    (z : ℂ) (x : RealHilbertComplexification E) :
    re (z • x) = z.re • re x - z.im • im x := rfl

@[simp] theorem im_smul [NormedAddCommGroup E] [Module ℝ E]
    (z : ℂ) (x : RealHilbertComplexification E) :
    im (z • x) = z.im • re x + z.re • im x := rfl

@[reducible] private def complexModule
    [NormedAddCommGroup E] [Module ℝ E] :
    Module ℂ (RealHilbertComplexification E) where
  smul := complexSMul
  one_smul x := by ext <;> simp
  mul_smul z w x := by
    ext <;> simp [Complex.mul_re, Complex.mul_im] <;> module
  smul_zero z := by ext <;> simp
  smul_add z x y := by ext <;> simp <;> module
  add_smul z w x := by ext <;> simp <;> module
  zero_smul x := by ext <;> simp

/-- The canonical complex inner product on the complexification. -/
def complexInner [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : RealHilbertComplexification E) : ℂ :=
  ((inner ℝ (re x) (re y) + inner ℝ (im x) (im y) : ℝ) : ℂ) +
    Complex.I *
      ((inner ℝ (re x) (im y) - inner ℝ (im x) (re y) : ℝ) : ℂ)

private theorem norm_complexSMul_sq
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : ℂ) (x : RealHilbertComplexification E) :
    ‖z • x‖ ^ 2 = ‖z‖ ^ 2 * ‖x‖ ^ 2 := by
  have hx : ‖x‖ ^ 2 = ‖re x‖ ^ 2 + ‖im x‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 x
  calc
    ‖z • x‖ ^ 2 =
        ‖z.re • re x - z.im • im x‖ ^ 2 +
          ‖z.im • re x + z.re • im x‖ ^ 2 :=
      WithLp.prod_norm_sq_eq_of_L2 (z • x)
    _ = ‖z‖ ^ 2 * (‖re x‖ ^ 2 + ‖im x‖ ^ 2) := by
      rw [norm_sub_sq_real, norm_add_sq_real]
      simp only [norm_smul, Real.norm_eq_abs,
        real_inner_smul_left, real_inner_smul_right]
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [mul_pow, sq_abs]
      ring
    _ = ‖z‖ ^ 2 * ‖x‖ ^ 2 := by rw [hx]

@[reducible] private def complexNormedSpace
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    NormedSpace ℂ (RealHilbertComplexification E) where
  __ := complexModule
  norm_smul_le z x := by
    have hsq := norm_complexSMul_sq z x
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    simpa [mul_pow] using le_of_eq hsq

instance [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    InnerProductSpace ℂ (RealHilbertComplexification E) where
  __ := complexNormedSpace
  inner := complexInner
  norm_sq_eq_re_inner x := by
    change ‖x‖ ^ 2 = (complexInner x x).re
    calc
      ‖x‖ ^ 2 = ‖re x‖ ^ 2 + ‖im x‖ ^ 2 :=
        WithLp.prod_norm_sq_eq_of_L2 x
      _ = (complexInner x x).re := by
        simp only [complexInner, Complex.add_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, zero_mul, one_mul, sub_self, add_zero]
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  conj_inner_symm x y := by
    apply Complex.ext <;>
      simp [complexInner, real_inner_comm]
  add_left x y z := by
    apply Complex.ext <;>
      simp [complexInner, inner_add_left] <;> ring
  smul_left x y z := by
    apply Complex.ext <;>
      simp [complexInner, Complex.mul_re, Complex.mul_im,
        inner_sub_left, inner_add_left, real_inner_smul_left] <;>
      ring

@[simp] theorem inner_apply
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : RealHilbertComplexification E) :
    inner ℂ x y = complexInner x y := rfl

@[simp] theorem complexInner_re
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : RealHilbertComplexification E) :
    (complexInner x y).re =
      inner ℝ (re x) (re y) + inner ℝ (im x) (im y) := by
  simp [complexInner]

@[simp] theorem complexInner_im
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : RealHilbertComplexification E) :
    (complexInner x y).im =
      inner ℝ (re x) (im y) - inner ℝ (im x) (re y) := by
  simp [complexInner]

end RealHilbertComplexification

end

end CarrySelfAdjointOperator

namespace LinearPMap

noncomputable section

open CarrySelfAdjointOperator
open CarrySelfAdjointOperator.RealHilbertComplexification

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Natural complex domain: both quadratures belong to the real domain. -/
def complexificationDomain (T : E →ₗ.[ℝ] F) :
    Submodule ℂ (RealHilbertComplexification E) where
  carrier := {x | re x ∈ T.domain ∧ im x ∈ T.domain}
  zero_mem' := by simp
  add_mem' hx hy := by
    exact ⟨T.domain.add_mem hx.1 hy.1,
      T.domain.add_mem hx.2 hy.2⟩
  smul_mem' z x hx := by
    exact ⟨T.domain.sub_mem
        (T.domain.smul_mem z.re hx.1)
        (T.domain.smul_mem z.im hx.2),
      T.domain.add_mem
        (T.domain.smul_mem z.im hx.1)
        (T.domain.smul_mem z.re hx.2)⟩

@[simp] theorem mem_complexificationDomain_iff
    (T : E →ₗ.[ℝ] F) (x : RealHilbertComplexification E) :
    x ∈ T.complexificationDomain ↔
      re x ∈ T.domain ∧ im x ∈ T.domain :=
  Iff.rfl

/-- Real-domain element carried by the real quadrature. -/
def complexificationDomainRe (T : E →ₗ.[ℝ] F)
    (x : T.complexificationDomain) : T.domain :=
  ⟨re x, x.property.1⟩

/-- Real-domain element carried by the imaginary quadrature. -/
def complexificationDomainIm (T : E →ₗ.[ℝ] F)
    (x : T.complexificationDomain) : T.domain :=
  ⟨im x, x.property.2⟩

@[simp] theorem complexificationDomainRe_add (T : E →ₗ.[ℝ] F)
    (x y : T.complexificationDomain) :
    T.complexificationDomainRe (x + y) =
      T.complexificationDomainRe x + T.complexificationDomainRe y := by
  apply Subtype.ext
  rfl

@[simp] theorem complexificationDomainIm_add (T : E →ₗ.[ℝ] F)
    (x y : T.complexificationDomain) :
    T.complexificationDomainIm (x + y) =
      T.complexificationDomainIm x + T.complexificationDomainIm y := by
  apply Subtype.ext
  rfl

@[simp] theorem complexificationDomainRe_smul (T : E →ₗ.[ℝ] F)
    (z : ℂ) (x : T.complexificationDomain) :
    T.complexificationDomainRe (z • x) =
      z.re • T.complexificationDomainRe x -
        z.im • T.complexificationDomainIm x := by
  apply Subtype.ext
  rfl

@[simp] theorem complexificationDomainIm_smul (T : E →ₗ.[ℝ] F)
    (z : ℂ) (x : T.complexificationDomain) :
    T.complexificationDomainIm (z • x) =
      z.im • T.complexificationDomainRe x +
        z.re • T.complexificationDomainIm x := by
  apply Subtype.ext
  rfl

/-- Coordinatewise complexification of a real partial linear operator. -/
def complexification (T : E →ₗ.[ℝ] F) :
    RealHilbertComplexification E →ₗ.[ℂ]
      RealHilbertComplexification F where
  domain := T.complexificationDomain
  toFun :=
    { toFun := fun x => RealHilbertComplexification.mk
        (T (T.complexificationDomainRe x))
        (T (T.complexificationDomainIm x))
      map_add' := fun x y => by
        ext
        · simp only [re_mk, re_add, complexificationDomainRe_add]
          exact T.map_add _ _
        · simp only [im_mk, im_add, complexificationDomainIm_add]
          exact T.map_add _ _
      map_smul' := fun z x => by
        ext
        · simp only [re_mk, re_smul, RingHom.id_apply,
            complexificationDomainRe_smul, im_mk]
          rw [T.map_sub, T.map_smul, T.map_smul]
        · simp only [im_mk, im_smul, RingHom.id_apply,
            complexificationDomainIm_smul, re_mk]
          rw [T.map_add, T.map_smul, T.map_smul] }

@[simp] theorem complexification_domain (T : E →ₗ.[ℝ] F) :
    T.complexification.domain = T.complexificationDomain :=
  rfl

@[simp] theorem re_complexification_apply (T : E →ₗ.[ℝ] F)
    (x : T.complexification.domain) :
    re (T.complexification x) =
      T (T.complexificationDomainRe x) :=
  rfl

@[simp] theorem im_complexification_apply (T : E →ₗ.[ℝ] F)
    (x : T.complexification.domain) :
    im (T.complexification x) =
      T (T.complexificationDomainIm x) :=
  rfl

/-- Product density is exactly density of the complexified natural domain. -/
theorem complexification_dense_domain
    (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    Dense (T.complexification.domain :
      Set (RealHilbertComplexification E)) := by
  have hprod : Dense ((T.domain : Set E) ×ˢ (T.domain : Set E)) :=
    hT.prod hT
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm
  have himage : Dense (e '' ((T.domain : Set E) ×ˢ
      (T.domain : Set E))) :=
    e.toHomeomorph.isDenseEmbedding.dense_image.mpr hprod
  have hset : e '' ((T.domain : Set E) ×ˢ (T.domain : Set E)) =
      (T.complexification.domain :
        Set (RealHilbertComplexification E)) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      refine ⟨WithLp.ofLp p, ?_, ?_⟩
      · exact hp
      · rfl
  rw [← hset]
  exact himage

/-- A real formal-adjoint identity complexifies without mixing or dropping
either quadrature. -/
theorem complexification_isFormalAdjoint
    (T : E →ₗ.[ℝ] F) (S : F →ₗ.[ℝ] E)
    (hformal : ∀ (x : T.domain) (y : S.domain),
      inner ℝ (T x) (y : F) = inner ℝ (x : E) (S y)) :
    T.complexification.IsFormalAdjoint S.complexification := by
  change ∀ (x : T.complexificationDomain)
      (y : S.complexificationDomain),
    inner ℂ (T.complexification x)
        (y : RealHilbertComplexification F) =
      inner ℂ (x : RealHilbertComplexification E)
        (S.complexification y)
  intro x y
  apply Complex.ext
  · simp only [inner_apply, complexInner_re,
      re_complexification_apply, im_complexification_apply]
    change
      inner ℝ (T (T.complexificationDomainRe x))
          ((S.complexificationDomainRe y : S.domain) : F) +
        inner ℝ (T (T.complexificationDomainIm x))
          ((S.complexificationDomainIm y : S.domain) : F) =
      inner ℝ ((T.complexificationDomainRe x : T.domain) : E)
          (S (S.complexificationDomainRe y)) +
        inner ℝ ((T.complexificationDomainIm x : T.domain) : E)
          (S (S.complexificationDomainIm y))
    rw [hformal, hformal]
  · simp only [inner_apply, complexInner_im,
      re_complexification_apply, im_complexification_apply]
    change
      inner ℝ (T (T.complexificationDomainRe x))
          ((S.complexificationDomainIm y : S.domain) : F) -
        inner ℝ (T (T.complexificationDomainIm x))
          ((S.complexificationDomainRe y : S.domain) : F) =
      inner ℝ ((T.complexificationDomainRe x : T.domain) : E)
          (S (S.complexificationDomainIm y)) -
        inner ℝ ((T.complexificationDomainIm x : T.domain) : E)
          (S (S.complexificationDomainRe y))
    rw [hformal, hformal]

variable [CompleteSpace E]

/-- The complex adjoint domain is exactly the complexification of the real
maximal-adjoint domain. -/
theorem complexification_adjoint_eq_realAdjoint
    (T : E →ₗ.[ℝ] E) (hT : Dense (T.domain : Set E)) :
    LinearPMap.adjoint T.complexification =
      (T.realAdjoint hT).complexification := by
  let TC := T.complexification
  let RA := T.realAdjoint hT
  let RAC := RA.complexification
  let TCA := LinearPMap.adjoint TC
  have hTC : Dense (TC.domain :
      Set (RealHilbertComplexification E)) :=
    T.complexification_dense_domain hT
  have hformal : TC.IsFormalAdjoint RAC := by
    exact T.complexification_isFormalAdjoint RA
      (T.realAdjoint_isFormalAdjoint hT)
  have hle : RAC ≤ TCA := hformal.le_adjoint hTC
  have hdomain : ∀ y : RealHilbertComplexification E,
      y ∈ TCA.domain → y ∈ RAC.domain := by
    intro y hy
    let yd : TCA.domain := ⟨y, hy⟩
    let w : RealHilbertComplexification E := TCA yd
    have hadj := TC.adjoint_isFormalAdjoint hTC yd
    constructor
    · change re y ∈ T.realAdjointDomain
      refine ⟨re w, fun x => ?_⟩
      let test : TC.domain :=
        ⟨RealHilbertComplexification.mk (x : E) 0, by
        exact ⟨x.property, T.domain.zero_mem⟩⟩
      have hTzero : ∀ h0 : (0 : E) ∈ T.domain,
          T ⟨0, h0⟩ = 0 := by
        intro h0
        rw [show (⟨0, h0⟩ : T.domain) = 0 by
          apply Subtype.ext
          rfl]
        exact T.map_zero
      have h := hadj test
      have hre := congrArg Complex.re h
      simpa [TC, TCA, yd, w, test, complexInner,
        complexificationDomainRe, complexificationDomainIm,
        hTzero] using hre
    · change im y ∈ T.realAdjointDomain
      refine ⟨im w, fun x => ?_⟩
      let test : TC.domain :=
        ⟨RealHilbertComplexification.mk (x : E) 0, by
        exact ⟨x.property, T.domain.zero_mem⟩⟩
      have hTzero : ∀ h0 : (0 : E) ∈ T.domain,
          T ⟨0, h0⟩ = 0 := by
        intro h0
        rw [show (⟨0, h0⟩ : T.domain) = 0 by
          apply Subtype.ext
          rfl]
        exact T.map_zero
      have h := hadj test
      have him := congrArg Complex.im h
      have hneg :
          -inner ℝ (im w) (x : E) =
            -inner ℝ (im y) (T x) := by
        simpa [TC, TCA, yd, w, test, complexInner,
          complexificationDomainRe, complexificationDomainIm,
          hTzero] using him
      linarith
  have hreverse : TCA ≤ RAC := by
    constructor
    · exact hdomain
    · intro y z hyz
      exact (hle.2 (x := z) (y := y) hyz.symm).symm
  exact le_antisymm hreverse hle

/-- Complex operator canonically associated with bundled maximal real
self-adjoint data. -/
def RealMaximalSelfAdjointData.complexification
    (data : RealMaximalSelfAdjointData E) :
    RealHilbertComplexification E →ₗ.[ℂ]
      RealHilbertComplexification E :=
  data.operator.complexification

omit [CompleteSpace E] in
/-- The complexified bundled operator retains the product natural domain. -/
theorem RealMaximalSelfAdjointData.complexification_dense_domain
    (data : RealMaximalSelfAdjointData E) :
    Dense (data.complexification.domain :
      Set (RealHilbertComplexification E)) :=
  data.operator.complexification_dense_domain data.denseDomain

/-- Maximal real self-adjointness transports to exact complex adjoint
equality, including equality of domains. -/
theorem RealMaximalSelfAdjointData.complexification_adjoint_eq
    (data : RealMaximalSelfAdjointData E) :
    LinearPMap.adjoint data.complexification =
      data.complexification := by
  rw [RealMaximalSelfAdjointData.complexification,
    complexification_adjoint_eq_realAdjoint
      data.operator data.denseDomain,
    data.adjoint_eq]

/-- The complexification is a self-adjoint complex partial operator. -/
theorem RealMaximalSelfAdjointData.complexification_isSelfAdjoint
    (data : RealMaximalSelfAdjointData E) :
    IsSelfAdjoint data.complexification := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact data.complexification_adjoint_eq

/-- The complexified maximal self-adjoint operator is closed. -/
theorem RealMaximalSelfAdjointData.complexification_isClosed
    (data : RealMaximalSelfAdjointData E) :
    data.complexification.IsClosed :=
  data.complexification_isSelfAdjoint.isClosed

end

end LinearPMap

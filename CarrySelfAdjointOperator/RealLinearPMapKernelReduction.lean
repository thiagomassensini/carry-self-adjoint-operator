import CarrySelfAdjointOperator.RealLinearPMapReciprocalBlock
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

/-!
# Canonical kernel reduction of closed real operators

For a closed densely defined real operator `T : E -> F`, its ambient kernel
is a closed subspace of `E`.  Restricting `T` to the orthogonal complement of
that kernel removes only its zero mode:

* the restricted operator is closed and injective;
* its domain is dense in the reduced Hilbert space;
* its range is exactly the original range; and
* projecting the original maximal adjoint gives a dense formal-adjoint core.

Consequently, when `T` and its maximal adjoint have dense domains and `T` has
dense range, the reciprocal off-diagonal block on the reduced source is
maximal self-adjoint without assuming that the original kernel vanishes.
-/

open scoped InnerProductSpace LinearPMap RealInnerProductSpace

namespace LinearPMap

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Kernel of a partial operator, viewed in its ambient source space. -/
def ambientKernel (T : E →ₗ.[ℝ] F) : Submodule ℝ E :=
  (LinearMap.ker T.toFun).map T.domain.subtype

theorem mem_ambientKernel_iff (T : E →ₗ.[ℝ] F) (x : E) :
    x ∈ T.ambientKernel ↔
      ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hzero⟩
    exact ⟨⟨x, hx⟩, hzero, rfl⟩

/-- The ambient kernel of a closed partial operator is closed. -/
theorem ambientKernel_isClosed
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed) :
    _root_.IsClosed (T.ambientKernel : Set E) := by
  have hpreimage : _root_.IsClosed
      ((fun x : E => (x, (0 : F))) ⁻¹' (T.graph : Set (E × F))) :=
    hClosed.preimage (continuous_id.prodMk continuous_const)
  convert hpreimage using 1
  ext x
  change x ∈ T.ambientKernel ↔ (x, (0 : F)) ∈ T.graph
  rw [T.mem_ambientKernel_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨hx, hzero⟩
    exact ⟨⟨x, hx⟩, rfl, hzero⟩
  · rintro ⟨y, hy, hzero⟩
    have hy' : (y : E) = x := hy
    subst x
    exact ⟨y.property, hzero⟩

/-- The ambient kernel bundled as a closed submodule. -/
def ambientKernelClosedSubmodule
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed) : ClosedSubmodule ℝ E where
  toSubmodule := T.ambientKernel
  isClosed' := T.ambientKernel_isClosed hClosed

/-- Canonical support of a closed partial operator: the orthogonal complement
of its ambient kernel. -/
abbrev kernelSupport
    (T : E →ₗ.[ℝ] F) (_hClosed : T.IsClosed) : Submodule ℝ E :=
  T.ambientKernelᗮ

/-- Restriction of a closed partial operator to its canonical nonzero support. -/
def kernelOrthogonalReduction
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed) :
    T.kernelSupport hClosed →ₗ.[ℝ] F where
  domain := T.domain.comap (T.kernelSupport hClosed).subtype
  toFun :=
    { toFun := fun x => T ⟨((x : T.kernelSupport hClosed) : E), x.property⟩
      map_add' := by
        intro x y
        rw [show (⟨((x + y : _) : E), (x + y).property⟩ : T.domain) =
            ⟨((x : _) : E), x.property⟩ +
              ⟨((y : _) : E), y.property⟩ by
          apply Subtype.ext
          rfl]
        exact T.map_add _ _
      map_smul' := by
        intro r x
        change T _ = r • T _
        rw [show (⟨((r • x : _) : E), (r • x).property⟩ : T.domain) =
            r • ⟨((x : _) : E), x.property⟩ by
          apply Subtype.ext
          rfl]
        exact T.map_smul r _ }

@[simp] theorem kernelOrthogonalReduction_apply
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed)
    (x : (T.kernelOrthogonalReduction hClosed).domain) :
    T.kernelOrthogonalReduction hClosed x =
      T ⟨((x : T.kernelSupport hClosed) : E), x.property⟩ :=
  rfl

/-- The reduced operator is injective by construction. -/
theorem kernelOrthogonalReduction_ker_eq_bot
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed) :
    LinearMap.ker (T.kernelOrthogonalReduction hClosed).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  apply Subtype.ext
  have hKernel : ((x : T.kernelSupport hClosed) : E) ∈ T.ambientKernel :=
    (T.mem_ambientKernel_iff _).2 ⟨x.property, hx⟩
  have hBoth : ((x : T.kernelSupport hClosed) : E) ∈
      T.ambientKernel ⊓ T.kernelSupport hClosed :=
    ⟨hKernel, x.val.property⟩
  change ((x : T.kernelSupport hClosed) : E) ∈
    T.ambientKernel ⊓ T.ambientKernelᗮ at hBoth
  rw [Submodule.inf_orthogonal_eq_bot] at hBoth
  exact hBoth

/-- Closedness is inherited by restriction to the closed support. -/
theorem kernelOrthogonalReduction_isClosed
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed) :
    (T.kernelOrthogonalReduction hClosed).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hpreimage : _root_.IsClosed
      ((fun p : T.kernelSupport hClosed × F =>
          (((p.1 : T.kernelSupport hClosed) : E), p.2)) ⁻¹'
        (T.graph : Set (E × F))) :=
    hClosed.preimage (continuous_subtype_val.prodMap continuous_id)
  convert hpreimage using 1
  ext p
  change p ∈ (T.kernelOrthogonalReduction hClosed).graph ↔
    (((p.1 : T.kernelSupport hClosed) : E), p.2) ∈ T.graph
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx, hvalue⟩
    exact ⟨⟨(x : T.kernelSupport hClosed), x.property⟩,
      congrArg Subtype.val hx, hvalue⟩
  · rintro ⟨x, hx, hvalue⟩
    have hxE : (x : E) = (p.1 : E) := hx
    have hpDomain : (p.1 : E) ∈ T.domain := by
      rw [← hxE]
      exact x.property
    refine ⟨⟨p.1, hpDomain⟩, rfl, ?_⟩
    change T ⟨(p.1 : E), hpDomain⟩ = p.2
    have hsubtype : (⟨(p.1 : E), hpDomain⟩ : T.domain) = x :=
      Subtype.ext hxE.symm
    simpa [hsubtype] using hvalue

section Complete

variable [CompleteSpace E]

/-- Orthogonal projection onto the canonical nonzero support. -/
def kernelSupportProjection
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed) :
    E →L[ℝ] T.kernelSupport hClosed := by
  letI : CompleteSpace T.ambientKernel :=
    (T.ambientKernel_isClosed hClosed).completeSpace_coe
  exact (T.kernelSupport hClosed).orthogonalProjectionOnto

theorem kernelSupportProjection_surjective
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed) :
    Function.Surjective (T.kernelSupportProjection hClosed) := by
  letI : CompleteSpace T.ambientKernel :=
    (T.ambientKernel_isClosed hClosed).completeSpace_coe
  intro x
  refine ⟨(x : E), ?_⟩
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr x.property

/-- Projecting a domain vector to the support keeps it in the domain. -/
theorem kernelSupportProjection_mem_reduction_domain
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed)
    (x : T.domain) :
    T.kernelSupportProjection hClosed (x : E) ∈
      (T.kernelOrthogonalReduction hClosed).domain := by
  letI : CompleteSpace T.ambientKernel :=
    (T.ambientKernel_isClosed hClosed).completeSpace_coe
  let K : ClosedSubmodule ℝ E := T.ambientKernelClosedSubmodule hClosed
  let p : E := (K : Submodule ℝ E).starProjection (x : E)
  have hpKernel : p ∈ T.ambientKernel := by
    exact (K : Submodule ℝ E).starProjection_apply_mem (x : E)
  rcases (T.mem_ambientKernel_iff p).1 hpKernel with ⟨hpDomain, hpZero⟩
  have hsupport :
      ((T.kernelSupportProjection hClosed (x : E) :
          T.kernelSupport hClosed) : E) = (x : E) - p := by
    change (T.kernelSupport hClosed).starProjection (x : E) = _
    have hsplit := (K : Submodule ℝ E).starProjection_add_starProjection_orthogonal (x : E)
    change (K : Submodule ℝ E)ᗮ.starProjection (x : E) = (x : E) - p
    dsimp only [p]
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsplit
  change ((T.kernelSupportProjection hClosed (x : E) :
    T.kernelSupport hClosed) : E) ∈ T.domain
  rw [hsupport]
  exact T.domain.sub_mem x.property hpDomain

/-- The reduced domain is dense in the support whenever the original domain
is dense in the ambient source. -/
theorem kernelOrthogonalReduction_dense_domain
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed)
    (hDomain : Dense (T.domain : Set E)) :
    Dense ((T.kernelOrthogonalReduction hClosed).domain :
      Set (T.kernelSupport hClosed)) := by
  let P := T.kernelSupportProjection hClosed
  have hPdense : Dense (P '' (T.domain : Set E)) :=
    (T.kernelSupportProjection_surjective hClosed).denseRange.dense_image
      P.continuous hDomain
  apply hPdense.mono
  rintro y ⟨x, hx, rfl⟩
  exact T.kernelSupportProjection_mem_reduction_domain hClosed ⟨x, hx⟩

/-- The reduction preserves every value of the original operator. -/
theorem kernelOrthogonalReduction_range_eq
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed) :
    LinearMap.range (T.kernelOrthogonalReduction hClosed).toFun =
      LinearMap.range T.toFun := by
  letI : CompleteSpace T.ambientKernel :=
    (T.ambientKernel_isClosed hClosed).completeSpace_coe
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨⟨((x : T.kernelSupport hClosed) : E), x.property⟩, rfl⟩
  · rintro y ⟨x, rfl⟩
    let q : (T.kernelOrthogonalReduction hClosed).domain :=
      ⟨T.kernelSupportProjection hClosed (x : E),
        T.kernelSupportProjection_mem_reduction_domain hClosed x⟩
    refine ⟨q, ?_⟩
    let K : ClosedSubmodule ℝ E := T.ambientKernelClosedSubmodule hClosed
    let p : E := (K : Submodule ℝ E).starProjection (x : E)
    have hpKernel : p ∈ T.ambientKernel := by
      exact (K : Submodule ℝ E).starProjection_apply_mem (x : E)
    rcases (T.mem_ambientKernel_iff p).1 hpKernel with ⟨hpDomain, hpZero⟩
    have hsupport :
        ((T.kernelSupportProjection hClosed (x : E) :
            T.kernelSupport hClosed) : E) = (x : E) - p := by
      change (T.kernelSupport hClosed).starProjection (x : E) = _
      have hsplit := (K : Submodule ℝ E).starProjection_add_starProjection_orthogonal (x : E)
      change (K : Submodule ℝ E)ᗮ.starProjection (x : E) = (x : E) - p
      dsimp only [p]
      rw [eq_sub_iff_add_eq, add_comm]
      exact hsplit
    change T ⟨((q : T.kernelSupport hClosed) : E), q.property⟩ = T x
    have hq : (⟨((q : T.kernelSupport hClosed) : E), q.property⟩ : T.domain) =
        x - ⟨p, hpDomain⟩ := by
      apply Subtype.ext
      exact hsupport
    rw [hq, T.map_sub, hpZero, sub_zero]

/-- Dense range is inherited unchanged by the canonical reduction. -/
theorem kernelOrthogonalReduction_dense_range
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F)) :
    Dense (LinearMap.range (T.kernelOrthogonalReduction hClosed).toFun :
      Set F) := by
  rw [T.kernelOrthogonalReduction_range_eq hClosed]
  exact hRange

/-- Projection of the original maximal adjoint to the reduced source. -/
def kernelOrthogonalReductionAdjointCore
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed)
    (hDomain : Dense (T.domain : Set E)) :
    F →ₗ.[ℝ] T.kernelSupport hClosed where
  domain := (T.realAdjoint hDomain).domain
  toFun :=
    { toFun := fun y => T.kernelSupportProjection hClosed
          (T.realAdjoint hDomain y)
      map_add' := by
        intro x y
        rw [(T.realAdjoint hDomain).map_add]
        exact (T.kernelSupportProjection hClosed).map_add _ _
      map_smul' := by
        intro r x
        rw [(T.realAdjoint hDomain).map_smul]
        exact (T.kernelSupportProjection hClosed).map_smul r _ }

/-- The projected adjoint core is formally adjoint to the reduced operator. -/
theorem kernelOrthogonalReductionAdjointCore_isFormalAdjoint
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed)
    (hDomain : Dense (T.domain : Set E)) :
    ∀ (x : (T.kernelOrthogonalReduction hClosed).domain)
      (y : (T.kernelOrthogonalReductionAdjointCore hClosed hDomain).domain),
      ⟪T.kernelOrthogonalReduction hClosed x, (y : F)⟫_ℝ =
        ⟪(x : T.kernelSupport hClosed),
          T.kernelOrthogonalReductionAdjointCore hClosed hDomain y⟫_ℝ := by
  letI : CompleteSpace T.ambientKernel :=
    (T.ambientKernel_isClosed hClosed).completeSpace_coe
  intro x y
  have hadj := T.realAdjoint_isFormalAdjoint hDomain
    ⟨((x : T.kernelSupport hClosed) : E), x.property⟩ y
  change ⟪T ⟨((x : T.kernelSupport hClosed) : E), x.property⟩,
      (y : F)⟫_ℝ = _
  rw [hadj]
  change ⟪((x : T.kernelSupport hClosed) : E),
      T.realAdjoint hDomain y⟫_ℝ =
    ⟪(x : T.kernelSupport hClosed),
      (T.kernelSupport hClosed).orthogonalProjectionOnto
        (T.realAdjoint hDomain y)⟫_ℝ
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (K := T.kernelSupport hClosed)
    (x : T.kernelSupport hClosed) (T.realAdjoint hDomain y)).symm

/-- The projected adjoint core is contained in the maximal adjoint of the
reduced operator. -/
theorem kernelOrthogonalReductionAdjointCore_le_realAdjoint
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed)
    (hDomain : Dense (T.domain : Set E)) :
    T.kernelOrthogonalReductionAdjointCore hClosed hDomain ≤
      (T.kernelOrthogonalReduction hClosed).realAdjoint
        (T.kernelOrthogonalReduction_dense_domain hClosed hDomain) := by
  exact (T.kernelOrthogonalReduction hClosed).le_realAdjoint_of_formalAdjoint
    (T.kernelOrthogonalReductionAdjointCore hClosed hDomain)
    (T.kernelOrthogonalReduction_dense_domain hClosed hDomain)
    (T.kernelOrthogonalReductionAdjointCore_isFormalAdjoint hClosed hDomain)

/-- Density of the original adjoint domain implies density of the reduced
maximal-adjoint domain. -/
theorem kernelOrthogonalReduction_realAdjoint_dense_domain
    (T : E →ₗ.[ℝ] F) (hClosed : T.IsClosed)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense ((T.realAdjoint hDomain).domain : Set F)) :
    Dense (((T.kernelOrthogonalReduction hClosed).realAdjoint
      (T.kernelOrthogonalReduction_dense_domain hClosed hDomain)).domain :
        Set F) := by
  exact hAdjointDomain.mono
    (T.kernelOrthogonalReductionAdjointCore_le_realAdjoint
      hClosed hDomain).1

variable [CompleteSpace F]

/-- A closed densely defined injective operator has adjoint with dense
range. -/
theorem realAdjoint_dense_range_of_isClosed_of_ker_eq_bot
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hClosed : T.IsClosed)
    (hKer : LinearMap.ker T.toFun = ⊥) :
    Dense (LinearMap.range (T.realAdjoint hDomain).toFun : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro x hx
  have hpair : ∀ z : (T.realAdjoint hDomain).domain,
      ⟪(0 : F), (z : F)⟫_ℝ = ⟪x, T.realAdjoint hDomain z⟫_ℝ := by
    intro z
    have horth := (Submodule.mem_orthogonal' _ _).1 hx
      (T.realAdjoint hDomain z) ⟨z, rfl⟩
    simpa using horth.symm
  have hgraph : (x, (0 : F)) ∈ T.graph :=
    T.mem_graph_of_forall_realAdjoint hDomain hClosed hpair
  rcases (LinearPMap.mem_graph_iff T).1 hgraph with ⟨xd, hxd, hzero⟩
  have hxdKer : xd ∈ LinearMap.ker T.toFun := by
    exact hzero
  rw [hKer] at hxdKer
  calc
    x = (xd : E) := hxd.symm
    _ = 0 := congrArg Subtype.val hxdKer

/-- Canonical maximal self-adjoint reciprocal block on the nonzero support of
a closed operator.  No hypothesis that the original kernel vanishes enters. -/
def reducedRealReciprocalOffDiagonalSelfAdjointData
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense ((T.realAdjoint hDomain).domain : Set F))
    (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F)) :
    RealMaximalSelfAdjointData
      (WithLp 2 (T.kernelSupport hClosed × F)) := by
  letI : CompleteSpace (T.kernelSupport hClosed) :=
    (T.ambientKernelClosedSubmodule hClosed : Submodule ℝ E).isClosed_orthogonal.completeSpace_coe
  let R := T.kernelOrthogonalReduction hClosed
  let hRDomain : Dense (R.domain : Set (T.kernelSupport hClosed)) :=
    T.kernelOrthogonalReduction_dense_domain hClosed hDomain
  let hRAdjointDomain : Dense ((R.realAdjoint hRDomain).domain : Set F) :=
    T.kernelOrthogonalReduction_realAdjoint_dense_domain
      hClosed hDomain hAdjointDomain
  have hRClosed : R.IsClosed :=
    T.kernelOrthogonalReduction_isClosed hClosed
  have hRRange : Dense (LinearMap.range R.toFun : Set F) :=
    T.kernelOrthogonalReduction_dense_range hClosed hRange
  have hRKer : LinearMap.ker R.toFun = ⊥ :=
    T.kernelOrthogonalReduction_ker_eq_bot hClosed
  have hRAdjointRange : Dense
      (LinearMap.range (R.realAdjoint hRDomain).toFun :
        Set (T.kernelSupport hClosed)) :=
    R.realAdjoint_dense_range_of_isClosed_of_ker_eq_bot
      hRDomain hRClosed hRKer
  exact R.realReciprocalOffDiagonalSelfAdjointData
    hRDomain hRAdjointDomain hRClosed hRRange hRAdjointRange hRKer

/-- An opaque carrier package for a canonical reduced self-adjoint operator.
Keeping the support as a field prevents concrete applications from unfolding
large operator expressions merely to elaborate the carrier type. -/
structure RealReducedMaximalSelfAdjointData (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  sourceSupport : Submodule ℝ E
  sourceSupport_isClosed : _root_.IsClosed (sourceSupport : Set E)
  selfAdjointData :
    RealMaximalSelfAdjointData (WithLp 2 (sourceSupport × F))

/-- Opaque-carrier form of the canonical kernel-reduced reciprocal block. -/
def reducedRealReciprocalOffDiagonalBundle
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense ((T.realAdjoint hDomain).domain : Set F))
    (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F)) :
    RealReducedMaximalSelfAdjointData E F where
  sourceSupport := T.kernelSupport hClosed
  sourceSupport_isClosed := Submodule.isClosed_orthogonal T.ambientKernel
  selfAdjointData := T.reducedRealReciprocalOffDiagonalSelfAdjointData
    hDomain hAdjointDomain hClosed hRange

end Complete

end

end LinearPMap

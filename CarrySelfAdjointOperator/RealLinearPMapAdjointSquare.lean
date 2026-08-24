import CarrySelfAdjointOperator.RealLinearPMapAdjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Maximal adjoint squares of closed real operators

For a closed densely defined real operator `T`, the natural maximal
composition `T* T` is positive and self-adjoint.  The central construction is
the orthogonal projection of `(f, 0)` onto the closed graph of `T`, which
proves surjectivity of `T* T + I` without a boundedness assumption.
-/

open scoped InnerProductSpace RealInnerProductSpace

namespace LinearPMap

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Graph of a real partial linear map in the Hilbert `L²` product. -/
def realGraphL2 (T : E →ₗ.[ℝ] F) :
    Submodule ℝ (WithLp 2 (E × F)) :=
  T.graph.map
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toLinearMap

theorem toLp_mem_realGraphL2 (T : E →ₗ.[ℝ] F) (x : T.domain) :
    WithLp.toLp 2 ((x : E), T x) ∈ T.realGraphL2 := by
  exact ⟨((x : E), T x),
    (LinearPMap.mem_graph_iff T).2 ⟨x, rfl, rfl⟩, rfl⟩

/-- A closed operator has a closed graph in the Hilbert `L²` product. -/
theorem realGraphL2_isClosed (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) :
    _root_.IsClosed (T.realGraphL2 : Set (WithLp 2 (E × F))) := by
  rw [realGraphL2, Submodule.map_coe]
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.isClosed_image.mpr hT

/-- The graph projection solves the positive resolvent equation
`(T* T + I)x = f`. -/
theorem exists_realAdjointSquare_add_eq
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDense : Dense (T.domain : Set E))
    (hClosed : T.IsClosed) (f : E) :
    ∃ x : (T.realAdjointSquare hDense).domain,
      T.realAdjointSquare hDense x + (x : E) = f := by
  let K := T.realGraphL2
  have hKclosed : _root_.IsClosed (K : Set (WithLp 2 (E × F))) :=
    T.realGraphL2_isClosed hClosed
  letI : CompleteSpace K := hKclosed.completeSpace_coe
  let u : WithLp 2 (E × F) := WithLp.toLp 2 (f, 0)
  let p : K := K.orthogonalProjectionOnto u
  rcases p.property with ⟨q, hqGraph, hqp⟩
  rcases (LinearPMap.mem_graph_iff T).mp hqGraph with
    ⟨x, hxq, hTxq⟩
  have hp : (p : WithLp 2 (E × F)) =
      WithLp.toLp 2 ((x : E), T x) := by
    rw [← hqp]
    apply congrArg (WithLp.toLp 2)
    exact Prod.ext hxq.symm hTxq.symm
  have hrepr : ∀ y : T.domain,
      ⟪f - (x : E), (y : E)⟫_ℝ = ⟪T x, T y⟫_ℝ := by
    intro y
    have horth := K.starProjection_inner_eq_zero u
      (WithLp.toLp 2 ((y : E), T y))
      (T.toLp_mem_realGraphL2 y)
    change
      ⟪u - (p : WithLp 2 (E × F)),
        WithLp.toLp 2 ((y : E), T y)⟫_ℝ = 0 at horth
    rw [hp] at horth
    have horth' :
        ⟪f, (y : E)⟫_ℝ =
          ⟪(x : E), (y : E)⟫_ℝ + ⟪T x, T y⟫_ℝ := by
      simpa [u, WithLp.prod_inner_apply, inner_sub_left,
        inner_neg_left, sub_eq_zero] using horth
    rw [inner_sub_left]
    linarith
  have hTxAdj : T x ∈ (T.realAdjoint hDense).domain := by
    change T x ∈ T.realAdjointDomain
    exact ⟨f - (x : E), hrepr⟩
  have hadj : T.realAdjoint hDense ⟨T x, hTxAdj⟩ =
      f - (x : E) :=
    T.realAdjoint_apply_eq hDense ⟨T x, hTxAdj⟩ hrepr
  let xsq : (T.realAdjointSquare hDense).domain :=
    realMaximalCompDomainMk (T.realAdjoint hDense) T x hTxAdj
  refine ⟨xsq, ?_⟩
  change T.realAdjoint hDense ⟨T x, hTxAdj⟩ + (x : E) = f
  rw [hadj, sub_add_cancel]

/-- Energy identity for the maximal adjoint square. -/
theorem realAdjointSquare_energyIdentity
    (T : E →ₗ.[ℝ] F)
    (hDense : Dense (T.domain : Set E))
    (x y : (T.realAdjointSquare hDense).domain) :
    ⟪T.realAdjointSquare hDense x, (y : E)⟫_ℝ =
      ⟪T (realMaximalCompFirstDomain (T.realAdjoint hDense) T x),
        T (realMaximalCompFirstDomain (T.realAdjoint hDense) T y)⟫_ℝ := by
  unfold realAdjointSquare at x y ⊢
  rw [realMaximalComp_apply]
  exact T.realAdjoint_inner hDense
    (realMaximalCompSecondDomain (T.realAdjoint hDense) T x)
    (realMaximalCompFirstDomain (T.realAdjoint hDense) T y)

/-- The maximal adjoint square is positive. -/
theorem realAdjointSquare_inner_nonneg
    (T : E →ₗ.[ℝ] F)
    (hDense : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDense).domain) :
    0 ≤ ⟪T.realAdjointSquare hDense x, (x : E)⟫_ℝ := by
  rw [T.realAdjointSquare_energyIdentity hDense x x]
  exact real_inner_self_nonneg

/-- The maximal adjoint square annihilates a domain vector exactly when the
original operator annihilates its retained first-domain component. -/
theorem realAdjointSquare_apply_eq_zero_iff
    (T : E →ₗ.[ℝ] F)
    (hDense : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDense).domain) :
    T.realAdjointSquare hDense x = 0 ↔
      T (realMaximalCompFirstDomain (T.realAdjoint hDense) T x) = 0 := by
  constructor
  · intro hx
    have henergy := T.realAdjointSquare_energyIdentity hDense x x
    rw [hx] at henergy
    have hself :
        ⟪T (realMaximalCompFirstDomain (T.realAdjoint hDense) T x),
          T (realMaximalCompFirstDomain
            (T.realAdjoint hDense) T x)⟫_ℝ = 0 := by
      simpa using henergy.symm
    exact inner_self_eq_zero.mp hself
  · intro hx
    unfold realAdjointSquare at x ⊢
    rw [realMaximalComp_apply]
    have hsecond :
        realMaximalCompSecondDomain (T.realAdjoint hDense) T x = 0 := by
      apply Subtype.ext
      exact hx
    rw [hsecond]
    exact (T.realAdjoint hDense).toFun.map_zero

/-- The standard kernel identity `ker (T* T) = ker T`, stated as the exact
trivial-kernel equivalence needed before inverse-square-root functional
calculus.  No closedness or completeness hypothesis is required. -/
theorem realAdjointSquare_ker_eq_bot_iff
    (T : E →ₗ.[ℝ] F)
    (hDense : Dense (T.domain : Set E)) :
    LinearMap.ker (T.realAdjointSquare hDense).toFun = ⊥ ↔
      LinearMap.ker T.toFun = ⊥ := by
  constructor
  · intro hSquare
    rw [LinearMap.ker_eq_bot'] at hSquare ⊢
    intro x hx
    have hxAdjoint : T x ∈ (T.realAdjoint hDense).domain := by
      have hx' : T x = 0 := hx
      rw [hx']
      exact Submodule.zero_mem _
    let xSquare : (T.realAdjointSquare hDense).domain :=
      realMaximalCompDomainMk (T.realAdjoint hDense) T x hxAdjoint
    have hxSquareZero : T.realAdjointSquare hDense xSquare = 0 :=
      (T.realAdjointSquare_apply_eq_zero_iff hDense xSquare).2 hx
    have hxSquare : xSquare = 0 := hSquare xSquare hxSquareZero
    apply Subtype.ext
    simpa [xSquare, realMaximalCompDomainMk] using
      congrArg Subtype.val hxSquare
  · intro hT
    rw [LinearMap.ker_eq_bot'] at hT ⊢
    intro x hx
    have hxFirst :
        realMaximalCompFirstDomain (T.realAdjoint hDense) T x = 0 :=
      hT _ ((T.realAdjointSquare_apply_eq_zero_iff hDense x).1 hx)
    apply Subtype.ext
    simpa [realMaximalCompFirstDomain] using congrArg Subtype.val hxFirst

/-- The maximal adjoint square is symmetric on its natural domain. -/
theorem realAdjointSquare_formalSelfAdjoint
    (T : E →ₗ.[ℝ] F)
    (hDense : Dense (T.domain : Set E)) :
    ∀ x y : (T.realAdjointSquare hDense).domain,
      ⟪T.realAdjointSquare hDense x, (y : E)⟫_ℝ =
        ⟪(x : E), T.realAdjointSquare hDense y⟫_ℝ := by
  intro x y
  calc
    ⟪T.realAdjointSquare hDense x, (y : E)⟫_ℝ =
        ⟪T (realMaximalCompFirstDomain (T.realAdjoint hDense) T x),
          T (realMaximalCompFirstDomain
            (T.realAdjoint hDense) T y)⟫_ℝ :=
      T.realAdjointSquare_energyIdentity hDense x y
    _ = ⟪T (realMaximalCompFirstDomain
          (T.realAdjoint hDense) T y),
        T (realMaximalCompFirstDomain
          (T.realAdjoint hDense) T x)⟫_ℝ := real_inner_comm _ _
    _ = ⟪T.realAdjointSquare hDense y, (x : E)⟫_ℝ :=
      (T.realAdjointSquare_energyIdentity hDense y x).symm
    _ = ⟪(x : E), T.realAdjointSquare hDense y⟫_ℝ :=
      real_inner_comm _ _

/-- The natural domain of `T* T` is dense.  Surjectivity of `T* T + I`
rules out a nonzero vector orthogonal to that domain. -/
theorem realAdjointSquare_dense_domain
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDense : Dense (T.domain : Set E))
    (hClosed : T.IsClosed) :
    Dense ((T.realAdjointSquare hDense).domain : Set E) := by
  let A := T.realAdjointSquare hDense
  let K := A.domain
  have hKorth : Kᗮ = (⊥ : Submodule ℝ E) := by
    apply le_antisymm
    · intro z hz
      rw [Submodule.mem_bot]
      rcases T.exists_realAdjointSquare_add_eq hDense hClosed z with
        ⟨x, hx⟩
      have hzx : ⟪z, (x : E)⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact hz x x.property
      have hsum :
          ⟪A x, (x : E)⟫_ℝ + ⟪(x : E), (x : E)⟫_ℝ = 0 := by
        rw [← inner_add_left, hx]
        exact hzx
      have hA_nonneg : 0 ≤ ⟪A x, (x : E)⟫_ℝ :=
        T.realAdjointSquare_inner_nonneg hDense x
      have hself_nonneg : 0 ≤ ⟪(x : E), (x : E)⟫_ℝ :=
        real_inner_self_nonneg
      have hxzero : (x : E) = 0 := by
        have hselfzero : ⟪(x : E), (x : E)⟫_ℝ = 0 := by
          linarith
        exact inner_self_eq_zero.mp hselfzero
      have hxSubtype : x = 0 := Subtype.ext hxzero
      rw [hxSubtype] at hx
      simpa using hx.symm
    · exact bot_le
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  let Kbar := K.topologicalClosure
  letI : CompleteSpace Kbar := inferInstance
  apply (Submodule.orthogonal_eq_bot_iff (K := Kbar)).mp
  simpa [Kbar, K, Submodule.orthogonal_closure] using hKorth

/-- Maximality of the symmetric adjoint square. -/
theorem realAdjointSquare_realAdjoint_le
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDense : Dense (T.domain : Set E))
    (hClosed : T.IsClosed) :
    let A := T.realAdjointSquare hDense
    let hA := T.realAdjointSquare_dense_domain hDense hClosed
    A.realAdjoint hA ≤ A := by
  dsimp only
  let A := T.realAdjointSquare hDense
  let hA : Dense (A.domain : Set E) :=
    T.realAdjointSquare_dense_domain hDense hClosed
  have hAle : A ≤ A.realAdjoint hA :=
    le_realAdjoint_of_formalAdjoint A A hA
      (T.realAdjointSquare_formalSelfAdjoint hDense)
  constructor
  · intro y hy
    let yd : (A.realAdjoint hA).domain := ⟨y, hy⟩
    let z : E := A.realAdjoint hA yd
    rcases T.exists_realAdjointSquare_add_eq hDense hClosed
        (z + y) with ⟨x, hx⟩
    let d : E := y - (x : E)
    rcases T.exists_realAdjointSquare_add_eq hDense hClosed d with
      ⟨u, hu⟩
    have hadjYu :
        ⟪z, (u : E)⟫_ℝ = ⟪y, A u⟫_ℝ :=
      A.realAdjoint_inner hA yd u
    have hsymXu :
        ⟪A x, (u : E)⟫_ℝ = ⟪(x : E), A u⟫_ℝ :=
      T.realAdjointSquare_formalSelfAdjoint hDense x u
    have hxInner := congrArg (fun v : E => ⟪v, (u : E)⟫_ℝ) hx
    have hdorth : ⟪d, A u + (u : E)⟫_ℝ = 0 := by
      dsimp only [d]
      rw [inner_add_right, inner_sub_left, inner_sub_left,
        ← hadjYu, ← hsymXu]
      simp only [inner_add_left] at hxInner
      linarith
    have hdself : ⟪d, d⟫_ℝ = 0 := by
      calc
        ⟪d, d⟫_ℝ = ⟪d, A u + (u : E)⟫_ℝ :=
          congrArg (fun v : E => ⟪d, v⟫_ℝ) hu.symm
        _ = 0 := hdorth
    have hdzero : d = 0 := inner_self_eq_zero.mp hdself
    have hyx : y = (x : E) := sub_eq_zero.mp hdzero
    rw [hyx]
    exact x.property
  · intro y x hyx
    have hy : y = Submodule.inclusion hAle.1 x := by
      apply Subtype.ext
      exact hyx
    rw [hy]
    exact (LinearPMap.apply_comp_inclusion hAle x).symm

/-- The maximal adjoint square of a closed densely defined real operator is
self-adjoint, expressed as literal equality with its maximal real adjoint. -/
theorem realAdjoint_realAdjointSquare_eq
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDense : Dense (T.domain : Set E))
    (hClosed : T.IsClosed) :
    let A := T.realAdjointSquare hDense
    let hA := T.realAdjointSquare_dense_domain hDense hClosed
    A.realAdjoint hA = A := by
  dsimp only
  let A := T.realAdjointSquare hDense
  let hA : Dense (A.domain : Set E) :=
    T.realAdjointSquare_dense_domain hDense hClosed
  apply le_antisymm
  · exact T.realAdjointSquare_realAdjoint_le hDense hClosed
  · exact le_realAdjoint_of_formalAdjoint A A hA
      (T.realAdjointSquare_formalSelfAdjoint hDense)

end

end LinearPMap

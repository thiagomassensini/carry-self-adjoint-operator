import CarrySelfAdjointOperator.LinearPMapMeromorphicResolvent
import CarrySelfAdjointOperator.RealLinearPMapKernelReduction
import Mathlib.Tactic

/-!
# Point spectrum of the reciprocal off-diagonal block

The exact two-step reciprocal identity already identifies the square of the
signed block on the range of `T* T`. This file polarizes that identity into
the two signed point eigenvectors and then passes them to the canonical
complexification.
-/

open scoped InnerProductSpace LinearPMap RealInnerProductSpace
open Filter Set Topology

namespace LinearPMap

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- An eigenvector of `T* T` with nonzero eigenvalue produces either signed
eigenvalue `mu` of the reciprocal off-diagonal block whenever
`mu ^ 2 * lambda = 1`.

The eigenvector is explicit. If `p = (T* T x, 0)` and `q = H p`, it is
`p + (mu * lambda) q`; the exact two-step law gives its eigenvalue equation. -/
theorem realReciprocalOffDiagonal_hasRealEigenvalue_of_adjointSquare
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hKer : LinearMap.ker T.toFun = ⊥)
    (hAdjointKer : LinearMap.ker
      (T.realAdjoint hDomain).toFun = ⊥)
    {lambda mu : ℝ} (hlambda : lambda ≠ 0)
    (hmu : mu ^ 2 * lambda = 1)
    (x : (T.realAdjointSquare hDomain).domain)
    (hx : (x : E) ≠ 0)
    (hAx : T.realAdjointSquare hDomain x = lambda • (x : E)) :
    HasRealEigenvalue (T.realReciprocalOffDiagonal hDomain) mu := by
  let H := T.realReciprocalOffDiagonal hDomain
  let p : H.domain :=
    T.realReciprocalOffDiagonalFirstSquareInput hDomain x
  let q : H.domain :=
    T.realReciprocalOffDiagonalSecondSquareInput hDomain hAdjointKer x
  let coefficient : ℝ := mu * lambda
  let eigenvector : H.domain := p + coefficient • q
  have hpApply : WithLp.ofLp (H p) =
      (0, T (T.realAdjointSquareFirstDomain hDomain x)) := by
    simpa only [H, p] using
      T.realReciprocalOffDiagonal_apply_firstSquareInput
        hDomain hAdjointKer x
  have hqApply : WithLp.ofLp (H q) = ((x : E), 0) := by
    simpa only [H, q] using
      T.realReciprocalOffDiagonal_apply_secondSquareInput
        hDomain hKer hAdjointKer x
  have hpValue : WithLp.ofLp (p : WithLp 2 (E × F)) =
      (T.realAdjointSquare hDomain x, 0) := rfl
  have hqValue : WithLp.ofLp (q : WithLp 2 (E × F)) =
      (0, T (T.realAdjointSquareFirstDomain hDomain x)) := by
    change WithLp.ofLp (H p) =
      (0, T (T.realAdjointSquareFirstDomain hDomain x))
    exact hpApply
  have heigenvectorValue :
      WithLp.ofLp (eigenvector : WithLp 2 (E × F)) =
        (T.realAdjointSquare hDomain x, 0) + coefficient •
          (0, T (T.realAdjointSquareFirstDomain hDomain x)) := by
    change WithLp.ofLp
      ((p : WithLp 2 (E × F)) + coefficient • (q : WithLp 2 (E × F))) = _
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, hpValue, hqValue]
  refine ⟨eigenvector, ?_, ?_⟩
  · intro hzero
    have hzero' := congrArg WithLp.ofLp hzero
    rw [heigenvectorValue] at hzero'
    have hfirst := congrArg Prod.fst hzero'
    simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_zero,
      WithLp.ofLp_zero] at hfirst
    rw [hAx] at hfirst
    simp only [smul_zero, add_zero] at hfirst
    exact hx ((smul_eq_zero.mp hfirst).resolve_left hlambda)
  · apply WithLp.ofLp_injective 2
    change WithLp.ofLp (H eigenvector) =
      WithLp.ofLp (mu • (eigenvector : WithLp 2 (E × F)))
    rw [show H eigenvector = H p + coefficient • H q by
      dsimp only [eigenvector]
      rw [H.map_add, H.map_smul]]
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, hpApply, hqApply,
      WithLp.ofLp_smul, heigenvectorValue]
    rw [hAx]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, zero_add]
    · dsimp only [coefficient]
      simp only [smul_zero, add_zero, smul_smul]
    · simp only [smul_zero, add_zero, smul_smul]
      change T (T.realAdjointSquareFirstDomain hDomain x) =
        (mu * coefficient) •
          T (T.realAdjointSquareFirstDomain hDomain x)
      rw [show mu * coefficient = 1 by
        dsimp only [coefficient]
        nlinarith [hmu]]
      exact (one_smul ℝ _).symm

/-- A real eigenmode of `T* T` also produces a genuinely complex signed
eigenvalue of the complexified reciprocal block whenever
`mu ^ 2 * lambda = 1`.  Unlike the real version above, this statement does
not assume in advance that the signed height `mu` is real. -/
theorem complexification_realReciprocalOffDiagonal_hasEigenvalue_of_adjointSquare_complex
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hKer : LinearMap.ker T.toFun = ⊥)
    (hAdjointKer : LinearMap.ker
      (T.realAdjoint hDomain).toFun = ⊥)
    {lambda : ℝ} {mu : ℂ} (hlambda : lambda ≠ 0)
    (hmu : mu ^ 2 * (lambda : ℂ) = 1)
    (x : (T.realAdjointSquare hDomain).domain)
    (hx : (x : E) ≠ 0)
    (hAx : T.realAdjointSquare hDomain x = lambda • (x : E)) :
    HasEigenvalue (T.realReciprocalOffDiagonal hDomain).complexification
      mu := by
  let H := T.realReciprocalOffDiagonal hDomain
  let p : H.domain :=
    T.realReciprocalOffDiagonalFirstSquareInput hDomain x
  let q : H.domain :=
    T.realReciprocalOffDiagonalSecondSquareInput hDomain hAdjointKer x
  let pc : H.complexification.domain :=
    ⟨CarrySelfAdjointOperator.RealHilbertComplexification.mk
        (p : WithLp 2 (E × F)) 0,
      ⟨p.property, H.domain.zero_mem⟩⟩
  let qc : H.complexification.domain :=
    ⟨CarrySelfAdjointOperator.RealHilbertComplexification.mk
        (q : WithLp 2 (E × F)) 0,
      ⟨q.property, H.domain.zero_mem⟩⟩
  let firstBlock : CarrySelfAdjointOperator.RealHilbertComplexification
      (WithLp 2 (E × F)) :=
    CarrySelfAdjointOperator.RealHilbertComplexification.mk
      (WithLp.toLp 2 ((x : E), 0)) 0
  let coefficient : ℂ := mu * (lambda : ℂ)
  let eigenvector : H.complexification.domain :=
    pc + coefficient • qc
  have hpcRe : H.complexificationDomainRe pc = p := by
    apply Subtype.ext
    rfl
  have hpcIm : H.complexificationDomainIm pc = 0 := by
    apply Subtype.ext
    rfl
  have hqcRe : H.complexificationDomainRe qc = q := by
    apply Subtype.ext
    rfl
  have hqcIm : H.complexificationDomainIm qc = 0 := by
    apply Subtype.ext
    rfl
  have hpApply : WithLp.ofLp (H p) =
      (0, T (T.realAdjointSquareFirstDomain hDomain x)) := by
    simpa only [H, p] using
      T.realReciprocalOffDiagonal_apply_firstSquareInput
        hDomain hAdjointKer x
  have hqApply : WithLp.ofLp (H q) = ((x : E), 0) := by
    simpa only [H, q] using
      T.realReciprocalOffDiagonal_apply_secondSquareInput
        hDomain hKer hAdjointKer x
  have hpcApply : H.complexification pc =
      (qc : CarrySelfAdjointOperator.RealHilbertComplexification
        (WithLp 2 (E × F))) := by
    apply CarrySelfAdjointOperator.RealHilbertComplexification.ext
    · rw [re_complexification_apply, hpcRe]
      rfl
    · rw [im_complexification_apply, hpcIm, H.map_zero]
      rfl
  have hqcApply : H.complexification qc = firstBlock := by
    apply CarrySelfAdjointOperator.RealHilbertComplexification.ext
    · rw [re_complexification_apply, hqcRe]
      exact WithLp.ofLp_injective 2 hqApply
    · rw [im_complexification_apply, hqcIm, H.map_zero]
      rfl
  have hpValue :
      (pc : CarrySelfAdjointOperator.RealHilbertComplexification
        (WithLp 2 (E × F))) = (lambda : ℂ) • firstBlock := by
    apply CarrySelfAdjointOperator.RealHilbertComplexification.ext
    · simp only [pc, firstBlock,
        CarrySelfAdjointOperator.RealHilbertComplexification.re_mk,
        CarrySelfAdjointOperator.RealHilbertComplexification.re_smul,
        Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
      apply WithLp.ofLp_injective 2
      rw [show WithLp.ofLp (p : WithLp 2 (E × F)) =
          (T.realAdjointSquare hDomain x, 0) by rfl,
        WithLp.ofLp_smul]
      exact Prod.ext hAx (by simp)
    · rw [CarrySelfAdjointOperator.RealHilbertComplexification.im_smul]
      simp [pc, firstBlock]
  refine ⟨eigenvector, ?_, ?_⟩
  · intro hzero
    dsimp only [eigenvector] at hzero
    change
      (pc : CarrySelfAdjointOperator.RealHilbertComplexification
        (WithLp 2 (E × F))) + coefficient •
          (qc : CarrySelfAdjointOperator.RealHilbertComplexification
            (WithLp 2 (E × F))) = 0 at hzero
    have hzero' :
        (pc : CarrySelfAdjointOperator.RealHilbertComplexification
          (WithLp 2 (E × F))) + coefficient •
            (qc : CarrySelfAdjointOperator.RealHilbertComplexification
              (WithLp 2 (E × F))) = 0 := by
      exact hzero
    have hre := congrArg
      CarrySelfAdjointOperator.RealHilbertComplexification.re hzero'
    rw [CarrySelfAdjointOperator.RealHilbertComplexification.re_add,
      CarrySelfAdjointOperator.RealHilbertComplexification.re_smul,
      CarrySelfAdjointOperator.RealHilbertComplexification.re_zero] at hre
    have hpcReValue :
        CarrySelfAdjointOperator.RealHilbertComplexification.re
          (pc : CarrySelfAdjointOperator.RealHilbertComplexification
            (WithLp 2 (E × F))) = (p : WithLp 2 (E × F)) := rfl
    have hqcReValue :
        CarrySelfAdjointOperator.RealHilbertComplexification.re
          (qc : CarrySelfAdjointOperator.RealHilbertComplexification
            (WithLp 2 (E × F))) = (q : WithLp 2 (E × F)) := rfl
    have hqcImValue :
        CarrySelfAdjointOperator.RealHilbertComplexification.im
          (qc : CarrySelfAdjointOperator.RealHilbertComplexification
            (WithLp 2 (E × F))) = 0 := rfl
    rw [hpcReValue, hqcReValue, hqcImValue, smul_zero, sub_zero] at hre
    have hfirst := congrArg
      (fun y : WithLp 2 (E × F) => (WithLp.ofLp y).1) hre
    have hqFirst : (WithLp.ofLp (q : WithLp 2 (E × F))).1 = 0 := by
      change (WithLp.ofLp (H p)).1 = 0
      rw [hpApply]
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, Prod.fst_add,
      Prod.smul_fst, hqFirst, smul_zero, add_zero] at hfirst
    change T.realAdjointSquare hDomain x = 0 at hfirst
    rw [hAx] at hfirst
    exact hx ((smul_eq_zero.mp hfirst).resolve_left hlambda)
  · change H.complexification (pc + coefficient • qc) =
      mu • ((pc : CarrySelfAdjointOperator.RealHilbertComplexification
        (WithLp 2 (E × F))) + coefficient •
          (qc : CarrySelfAdjointOperator.RealHilbertComplexification
            (WithLp 2 (E × F))))
    rw [H.complexification.map_add, H.complexification.map_smul,
      hpcApply, hqcApply, hpValue]
    have hmuc : mu * coefficient = 1 := by
      dsimp only [coefficient]
      rw [← mul_assoc, ← pow_two, hmu]
    rw [smul_add, smul_smul, smul_smul, hmuc, one_smul]
    dsimp only [coefficient]
    rw [mul_smul]
    exact add_comm _ _

/-- A nonzero point eigenmode of `T* T` lies in the canonical orthogonal
kernel support and remains an eigenmode of the maximal adjoint square after
kernel reduction. Thus the reduction removes only the zero mode. -/
theorem exists_kernelOrthogonalReduction_adjointSquare_eigenvector
    [CompleteSpace E]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hClosed : T.IsClosed)
    {lambda : ℝ} (hlambda : lambda ≠ 0)
    (x : (T.realAdjointSquare hDomain).domain)
    (hx : (x : E) ≠ 0)
    (hAx : T.realAdjointSquare hDomain x = lambda • (x : E)) :
    let R := T.kernelOrthogonalReduction hClosed
    let hRDomain := T.kernelOrthogonalReduction_dense_domain hClosed hDomain
    ∃ xr : (R.realAdjointSquare hRDomain).domain,
      (xr : T.kernelSupport hClosed) ≠ 0 ∧
      R.realAdjointSquare hRDomain xr =
        lambda • (xr : T.kernelSupport hClosed) := by
  dsimp only
  let R := T.kernelOrthogonalReduction hClosed
  let hRDomain : Dense (R.domain : Set (T.kernelSupport hClosed)) :=
    T.kernelOrthogonalReduction_dense_domain hClosed hDomain
  have hxSupport : (x : E) ∈ T.kernelSupport hClosed := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    rcases (T.mem_ambientKernel_iff y).1 hy with ⟨hyDomain, hTy⟩
    let yd : T.domain := ⟨y, hyDomain⟩
    have hadj := T.realAdjoint_inner hDomain
      (T.realAdjointSquareSecondDomain hDomain x) yd
    rw [← T.realAdjointSquare_apply_retained hDomain x, hAx, hTy] at hadj
    simp only [real_inner_smul_left, inner_zero_right] at hadj
    exact (mul_eq_zero.mp hadj).resolve_left hlambda
  let xr₀ : T.kernelSupport hClosed := ⟨(x : E), hxSupport⟩
  let xd : R.domain := ⟨xr₀, by
    change (x : E) ∈ T.domain
    exact (T.realAdjointSquareFirstDomain hDomain x).property⟩
  let yAdj : (T.realAdjoint hDomain).domain :=
    T.realAdjointSquareSecondDomain hDomain x
  let C := T.kernelOrthogonalReductionAdjointCore hClosed hDomain
  let RA := R.realAdjoint hRDomain
  have hCle : C ≤ RA :=
    T.kernelOrthogonalReductionAdjointCore_le_realAdjoint
      hClosed hDomain
  have hRxd : R xd = (yAdj : F) := by
    rfl
  have hRxdAdj : R xd ∈ RA.domain := by
    rw [hRxd]
    exact hCle.1 yAdj.property
  let xr : (R.realAdjointSquare hRDomain).domain :=
    realMaximalCompDomainMk RA R xd hRxdAdj
  refine ⟨xr, ?_, ?_⟩
  · change (xr₀ : T.kernelSupport hClosed) ≠ 0
    intro hzero
    apply hx
    exact congrArg Subtype.val hzero
  · change RA ⟨R xd, hRxdAdj⟩ =
      lambda • (xr₀ : T.kernelSupport hClosed)
    let yi : RA.domain := Submodule.inclusion hCle.1 yAdj
    have hyDomain : (⟨R xd, hRxdAdj⟩ : RA.domain) = yi := by
      apply Subtype.ext
      exact hRxd
    rw [hyDomain]
    rw [← LinearPMap.apply_comp_inclusion hCle yAdj]
    change T.kernelSupportProjection hClosed
        (T.realAdjoint hDomain yAdj) = lambda • xr₀
    rw [← T.realAdjointSquare_apply_retained hDomain x, hAx,
      (T.kernelSupportProjection hClosed).map_smul]
    apply congrArg (fun v => lambda • v)
    apply Subtype.ext
    change (T.kernelSupport hClosed).starProjection (x : E) = (x : E)
    exact Submodule.starProjection_eq_self_iff.mpr hxSupport

/-- Complex point-spectrum form of the reciprocal-block transport. -/
theorem complexification_realReciprocalOffDiagonal_hasEigenvalue_of_adjointSquare
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hKer : LinearMap.ker T.toFun = ⊥)
    (hAdjointKer : LinearMap.ker
      (T.realAdjoint hDomain).toFun = ⊥)
    {lambda mu : ℝ} (hlambda : lambda ≠ 0)
    (hmu : mu ^ 2 * lambda = 1)
    (x : (T.realAdjointSquare hDomain).domain)
    (hx : (x : E) ≠ 0)
    (hAx : T.realAdjointSquare hDomain x = lambda • (x : E)) :
    HasEigenvalue (T.realReciprocalOffDiagonal hDomain).complexification
      (mu : ℂ) := by
  exact complexification_hasEigenvalue_of_hasRealEigenvalue
    (T.realReciprocalOffDiagonal_hasRealEigenvalue_of_adjointSquare
      hDomain hKer hAdjointKer hlambda hmu x hx hAx)

/-- Full nonzero-mode transport through canonical kernel reduction and the
complexified reciprocal block. This is the operator-theoretic passage from a
positive `T* T` eigenmode to a signed-height eigenvalue; no zero-kernel
hypothesis on the original `T` is required. -/
theorem complexification_kernelReducedReciprocal_hasEigenvalue_of_adjointSquare
    [CompleteSpace E]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F))
    {lambda mu : ℝ} (hlambda : lambda ≠ 0)
    (hmu : mu ^ 2 * lambda = 1)
    (x : (T.realAdjointSquare hDomain).domain)
    (hx : (x : E) ≠ 0)
    (hAx : T.realAdjointSquare hDomain x = lambda • (x : E)) :
    let R := T.kernelOrthogonalReduction hClosed
    let hRDomain := T.kernelOrthogonalReduction_dense_domain hClosed hDomain
    HasEigenvalue (R.realReciprocalOffDiagonal hRDomain).complexification
      (mu : ℂ) := by
  dsimp only
  let R := T.kernelOrthogonalReduction hClosed
  let hRDomain : Dense (R.domain : Set (T.kernelSupport hClosed)) :=
    T.kernelOrthogonalReduction_dense_domain hClosed hDomain
  have hRKer : LinearMap.ker R.toFun = ⊥ :=
    T.kernelOrthogonalReduction_ker_eq_bot hClosed
  have hRRange : Dense (LinearMap.range R.toFun : Set F) :=
    T.kernelOrthogonalReduction_dense_range hClosed hRange
  have hRAdjointKer : LinearMap.ker
      (R.realAdjoint hRDomain).toFun = ⊥ :=
    R.realAdjoint_ker_eq_bot_of_denseRange hRDomain hRRange
  obtain ⟨xr, hxr, hRx⟩ :=
    T.exists_kernelOrthogonalReduction_adjointSquare_eigenvector
      hDomain hClosed hlambda x hx hAx
  exact R.complexification_realReciprocalOffDiagonal_hasEigenvalue_of_adjointSquare
    hRDomain hRKer hRAdjointKer hlambda hmu xr hxr hRx

/-- Complex signed-height transport through canonical kernel reduction.  The
positive-square eigenvalue remains real, but the reciprocal signed root is
allowed to be complex until self-adjointness of the reduced block forces its
reality. -/
theorem complexification_kernelReducedReciprocal_hasEigenvalue_of_adjointSquare_complex
    [CompleteSpace E]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F))
    {lambda : ℝ} {mu : ℂ} (hlambda : lambda ≠ 0)
    (hmu : mu ^ 2 * (lambda : ℂ) = 1)
    (x : (T.realAdjointSquare hDomain).domain)
    (hx : (x : E) ≠ 0)
    (hAx : T.realAdjointSquare hDomain x = lambda • (x : E)) :
    let R := T.kernelOrthogonalReduction hClosed
    let hRDomain := T.kernelOrthogonalReduction_dense_domain hClosed hDomain
    HasEigenvalue (R.realReciprocalOffDiagonal hRDomain).complexification
      mu := by
  dsimp only
  let R := T.kernelOrthogonalReduction hClosed
  let hRDomain : Dense (R.domain : Set (T.kernelSupport hClosed)) :=
    T.kernelOrthogonalReduction_dense_domain hClosed hDomain
  have hRKer : LinearMap.ker R.toFun = ⊥ :=
    T.kernelOrthogonalReduction_ker_eq_bot hClosed
  have hRRange : Dense (LinearMap.range R.toFun : Set F) :=
    T.kernelOrthogonalReduction_dense_range hClosed hRange
  have hRAdjointKer : LinearMap.ker
      (R.realAdjoint hRDomain).toFun = ⊥ :=
    R.realAdjoint_ker_eq_bot_of_denseRange hRDomain hRRange
  obtain ⟨xr, hxr, hRx⟩ :=
    T.exists_kernelOrthogonalReduction_adjointSquare_eigenvector
      hDomain hClosed hlambda x hx hAx
  exact
    R.complexification_realReciprocalOffDiagonal_hasEigenvalue_of_adjointSquare_complex
      hRDomain hRKer hRAdjointKer hlambda hmu xr hxr hRx

/-- Bundled form of the complex signed-root transport.  Its target is exactly
the complexification exported by the canonical reduced maximal self-adjoint
package. -/
theorem reducedRealReciprocalOffDiagonalSelfAdjointData_hasEigenvalue_of_adjointSquare_complex
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense ((T.realAdjoint hDomain).domain : Set F))
    (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F))
    {lambda : ℝ} {mu : ℂ} (hlambda : lambda ≠ 0)
    (hmu : mu ^ 2 * (lambda : ℂ) = 1)
    (x : (T.realAdjointSquare hDomain).domain)
    (hx : (x : E) ≠ 0)
    (hAx : T.realAdjointSquare hDomain x = lambda • (x : E)) :
    HasEigenvalue
      (T.reducedRealReciprocalOffDiagonalSelfAdjointData
        hDomain hAdjointDomain hClosed hRange).complexification mu := by
  let R := T.kernelOrthogonalReduction hClosed
  let hRDomain : Dense (R.domain : Set (T.kernelSupport hClosed)) :=
    T.kernelOrthogonalReduction_dense_domain hClosed hDomain
  change HasEigenvalue (R.realReciprocalOffDiagonal hRDomain).complexification mu
  exact T.complexification_kernelReducedReciprocal_hasEigenvalue_of_adjointSquare_complex
    hDomain hClosed hRange hlambda hmu x hx hAx

/-- End-to-end operator-theoretic pole transport. A meromorphic graph
resolvent of the complexified positive square at `lambda⁻¹`, detected by a
bounded linear readout, yields the signed point eigenvalue `mu` of the
kernel-reduced reciprocal operator whenever `mu² lambda = 1`.

All domain, graph, complexification, reduction, and sign transports are
discharged here. A concrete application only has to supply the global
vector-valued graph resolvent and its scalar readout identification. -/
theorem complexification_kernelReducedReciprocal_hasEigenvalue_of_meromorphicGraphResolvent
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F))
    {lambda mu : ℝ} (hlambda : lambda ≠ 0)
    (hmu : mu ^ 2 * lambda = 1)
    {graphResolvent : ℂ →
      CarrySelfAdjointOperator.RealHilbertComplexification E ×
        CarrySelfAdjointOperator.RealHilbertComplexification E}
    {source : CarrySelfAdjointOperator.RealHilbertComplexification E}
    (hmeromorphic : MeromorphicAt graphResolvent ((lambda⁻¹ : ℝ) : ℂ))
    (readout :
      (CarrySelfAdjointOperator.RealHilbertComplexification E ×
        CarrySelfAdjointOperator.RealHilbertComplexification E) →L[ℂ] ℂ)
    (hreadout : Tendsto (fun z => readout (graphResolvent z))
      (nhdsWithin ((lambda⁻¹ : ℝ) : ℂ) {((lambda⁻¹ : ℝ) : ℂ)}ᶜ)
      (Bornology.cobounded ℂ))
    (hgraph : ∀ᶠ z in
      nhdsWithin ((lambda⁻¹ : ℝ) : ℂ) {((lambda⁻¹ : ℝ) : ℂ)}ᶜ,
      graphResolvent z ∈
        (T.realAdjointSquare hDomain).complexification.graph)
    (hresolvent : ∀ᶠ z in
      nhdsWithin ((lambda⁻¹ : ℝ) : ℂ) {((lambda⁻¹ : ℝ) : ℂ)}ᶜ,
      (graphResolvent z).1 - z • (graphResolvent z).2 = source) :
    let R := T.kernelOrthogonalReduction hClosed
    let hRDomain := T.kernelOrthogonalReduction_dense_domain hClosed hDomain
    HasEigenvalue (R.realReciprocalOffDiagonal hRDomain).complexification
      (mu : ℂ) := by
  dsimp only
  let A := T.realAdjointSquare hDomain
  let hADomain : Dense (A.domain : Set E) :=
    T.realAdjointSquare_dense_domain hDomain hClosed
  let data : RealMaximalSelfAdjointData E := {
    operator := A
    denseDomain := hADomain
    adjoint_eq := T.realAdjoint_realAdjointSquare_eq hDomain hClosed }
  have hAClosed : A.complexification.IsClosed := by
    exact data.complexification_isClosed
  have hcenter : ((lambda⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero hlambda
  have hcomplexEigen :
      HasEigenvalue A.complexification (((lambda⁻¹ : ℝ) : ℂ)⁻¹) := by
    exact hasEigenvalue_inv_of_meromorphic_graphResolvent_readout
      A.complexification hAClosed hcenter hmeromorphic readout hreadout
        hgraph hresolvent
  have hparameter : (((lambda⁻¹ : ℝ) : ℂ)⁻¹ = (lambda : ℂ)) := by
    simp
  rw [hparameter] at hcomplexEigen
  have hrealEigen : HasRealEigenvalue A lambda :=
    hasRealEigenvalue_of_complexification_hasEigenvalue hcomplexEigen
  obtain ⟨x, hx, hAx⟩ := hrealEigen
  exact T.complexification_kernelReducedReciprocal_hasEigenvalue_of_adjointSquare
    hDomain hClosed hRange hlambda hmu x hx hAx

end

end LinearPMap

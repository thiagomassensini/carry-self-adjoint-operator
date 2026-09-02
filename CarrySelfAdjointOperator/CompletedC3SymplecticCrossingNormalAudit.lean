import CarrySelfAdjointOperator.CompletedC3SymplecticCrossingTangentAudit
import CarrySelfAdjointOperator.CompletedC3FullWronskianPolarization
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# Riesz normal of the completed C3 symplectic crossing

This file identifies the fixed-center crossing functional with its canonical
Riesz vector and tests only the energy of the orthogonal projection onto that
normal line.  It introduces no Hessian, clock quotient, provenance quotient,
theta representation, zero hypothesis, confinement statement, higher moment,
Hankel matrix, or Jacobi operator.
-/

open scoped ComplexConjugate InnerProduct InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## The old full operator is a unitary quarter turn -/

/-- The adjoint of the full Wronskian complex structure is its negative. -/
theorem canonicalCompletedC3FullWronskianOperator_adjoint_eq_neg :
    canonicalCompletedC3FullWronskianOperator.adjoint =
      -canonicalCompletedC3FullWronskianOperator := by
  have hnegAdjoint :
      -canonicalCompletedC3FullWronskianOperator =
        canonicalCompletedC3FullWronskianOperator.adjoint := by
    apply (ContinuousLinearMap.eq_adjoint_iff
      (-canonicalCompletedC3FullWronskianOperator)
      canonicalCompletedC3FullWronskianOperator).2
    intro x y
    rw [neg_apply, inner_neg_left,
      inner_canonicalCompletedC3FullWronskianOperator_left]
    ring
  exact hnegAdjoint.symm

/-- Consequently `J_full* J_full = I`. -/
theorem canonicalCompletedC3FullWronskianOperator_adjoint_comp_self :
    canonicalCompletedC3FullWronskianOperator.adjoint.comp
        canonicalCompletedC3FullWronskianOperator =
      ContinuousLinearMap.id ℂ
        CanonicalCompletedC3FullWronskianOperatorCarrier := by
  ext state
  rw [canonicalCompletedC3FullWronskianOperator_adjoint_eq_neg,
    ContinuousLinearMap.comp_apply, neg_apply,
    canonicalCompletedC3FullWronskianOperator_sq]
  simp

/-- The full Wronskian operator preserves the Hilbert norm exactly. -/
theorem norm_canonicalCompletedC3FullWronskianOperator
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    ‖canonicalCompletedC3FullWronskianOperator state‖ = ‖state‖ := by
  exact
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      canonicalCompletedC3FullWronskianOperator).2
        canonicalCompletedC3FullWronskianOperator_adjoint_comp_self state

/-- In particular the full complex structure is an isometry. -/
theorem canonicalCompletedC3FullWronskianOperator_isometry :
    Isometry canonicalCompletedC3FullWronskianOperator := by
  exact
    (ContinuousLinearMap.isometry_iff_adjoint_comp_self
      canonicalCompletedC3FullWronskianOperator).2
        canonicalCompletedC3FullWronskianOperator_adjoint_comp_self

/-- The operator norm is therefore exactly one. -/
theorem norm_canonicalCompletedC3FullWronskianOperator_eq_one :
    ‖canonicalCompletedC3FullWronskianOperator‖ = 1 := by
  let jIso :
      CanonicalCompletedC3FullWronskianOperatorCarrier →ₗᵢ[ℂ]
        CanonicalCompletedC3FullWronskianOperatorCarrier :=
    { toLinearMap := canonicalCompletedC3FullWronskianOperator.toLinearMap
      norm_map' := norm_canonicalCompletedC3FullWronskianOperator }
  have hmap : jIso.toContinuousLinearMap =
      canonicalCompletedC3FullWronskianOperator := by
    ext state
    rfl
  rw [← hmap]
  exact jIso.norm_toContinuousLinearMap

/-! ## Cutoff-free central state, tangent, and crossing functional -/

/-- The central full state in its cutoff-free analytic spelling. -/
def canonicalCompletedC3FullWronskianCentralState :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  canonicalCompletedC3FullWronskianAnalyticState 0

/-- Every cutoff state is literally the same central vector after the old
completed trace projection. -/
theorem canonicalCompletedC3FullWronskianOperatorState_zero_eq_centralState
    (M : ℕ) :
    canonicalCompletedC3FullWronskianOperatorState M 0 =
      canonicalCompletedC3FullWronskianCentralState := by
  exact canonicalCompletedC3FullWronskianOperatorState_eq_analyticState M
    zero_mem_completedNativeHeightDomain

/-- Cutoff-free real tangent of the analytic full source curve. -/
def canonicalCompletedC3FullWronskianRealSourceTangent :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  deriv
    (fun t : ℝ => canonicalCompletedC3FullWronskianAnalyticState (t : ℂ)) 0

/-- The tangent named with a cutoff in the preceding audit is independent of
that cutoff. -/
theorem canonicalCompletedC3FullWronskianOperatorRealSourceTangent_eq
    (M : ℕ) :
    canonicalCompletedC3FullWronskianOperatorRealSourceTangent M =
      canonicalCompletedC3FullWronskianRealSourceTangent := by
  unfold canonicalCompletedC3FullWronskianOperatorRealSourceTangent
    canonicalCompletedC3FullWronskianRealSourceTangent
  congr 1
  funext t
  exact canonicalCompletedC3FullWronskianOperatorState_eq_analyticState M
    (ofReal_mem_completedNativeHeightDomain t)

/-- The cutoff-free crossing functional obtained by fixing the central
response leg. -/
def canonicalCompletedC3FullOperatorCrossingFunctional :
    CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ] ℂ :=
  (innerSL ℂ canonicalCompletedC3FullWronskianCentralState).comp
    canonicalCompletedC3FullWronskianOperator

/-- The preceding cutoff-indexed functional is the same fixed functional for
every `M`. -/
theorem canonicalCompletedC3FullOperatorCentralCrossingFunctional_eq
    (M : ℕ) :
    canonicalCompletedC3FullOperatorCentralCrossingFunctional M =
      canonicalCompletedC3FullOperatorCrossingFunctional := by
  unfold canonicalCompletedC3FullOperatorCentralCrossingFunctional
    canonicalCompletedC3FullOperatorCrossingFunctional
  rw [canonicalCompletedC3FullWronskianOperatorState_zero_eq_centralState]

/-! ## The canonical Riesz normal -/

/-- Cutoff-indexed Riesz representer of the functional `L_M`. -/
def canonicalCompletedC3FullOperatorCrossingNormalAtCutoff
    (M : ℕ) : CanonicalCompletedC3FullWronskianOperatorCarrier :=
  canonicalCompletedC3FullWronskianOperator.adjoint
    (canonicalCompletedC3FullWronskianOperatorState M 0)

/-- At every cutoff, skew-adjointness gives the requested concrete formula
`n_M = -J_full X_full,M(0)`. -/
theorem canonicalCompletedC3FullOperatorCrossingNormalAtCutoff_eq_neg_operator
    (M : ℕ) :
    canonicalCompletedC3FullOperatorCrossingNormalAtCutoff M =
      -canonicalCompletedC3FullWronskianOperator
        (canonicalCompletedC3FullWronskianOperatorState M 0) := by
  unfold canonicalCompletedC3FullOperatorCrossingNormalAtCutoff
  rw [canonicalCompletedC3FullWronskianOperator_adjoint_eq_neg, neg_apply]

/-- `n_M` is exactly the Riesz vector of the old cutoff-indexed functional. -/
theorem canonicalCompletedC3FullOperatorCentralCrossingFunctional_apply_eq_inner_normal
    (M : ℕ) (v : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullOperatorCentralCrossingFunctional M v =
      inner ℂ (canonicalCompletedC3FullOperatorCrossingNormalAtCutoff M) v := by
  unfold canonicalCompletedC3FullOperatorCentralCrossingFunctional
    canonicalCompletedC3FullOperatorCrossingNormalAtCutoff
  change inner ℂ (canonicalCompletedC3FullWronskianOperatorState M 0)
      (canonicalCompletedC3FullWronskianOperator v) = _
  exact
    (canonicalCompletedC3FullWronskianOperator.adjoint_inner_left v
      (canonicalCompletedC3FullWronskianOperatorState M 0)).symm

/-- Cutoff-indexed null hyperplane. -/
theorem canonicalCompletedC3FullOperatorCentralCrossingFunctional_ker
    (M : ℕ) :
    (canonicalCompletedC3FullOperatorCentralCrossingFunctional M).ker =
      (ℂ ∙ canonicalCompletedC3FullOperatorCrossingNormalAtCutoff M)ᗮ := by
  ext v
  rw [LinearMap.mem_ker]
  change canonicalCompletedC3FullOperatorCentralCrossingFunctional M v = 0 ↔ _
  rw [
    canonicalCompletedC3FullOperatorCentralCrossingFunctional_apply_eq_inner_normal,
    Submodule.mem_orthogonal_singleton_iff_inner_right]

/-- Riesz representer of the crossing functional.  The adjoint is part of
the definition, so this definition does not presuppose skew-adjointness. -/
def canonicalCompletedC3FullOperatorCrossingNormal :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  canonicalCompletedC3FullWronskianOperator.adjoint
    canonicalCompletedC3FullWronskianCentralState

/-- The cutoff-indexed Riesz normals are all the same cutoff-free vector. -/
theorem canonicalCompletedC3FullOperatorCrossingNormalAtCutoff_eq
    (M : ℕ) :
    canonicalCompletedC3FullOperatorCrossingNormalAtCutoff M =
      canonicalCompletedC3FullOperatorCrossingNormal := by
  unfold canonicalCompletedC3FullOperatorCrossingNormalAtCutoff
    canonicalCompletedC3FullOperatorCrossingNormal
  rw [canonicalCompletedC3FullWronskianOperatorState_zero_eq_centralState]

/-- Skew-adjointness turns the abstract Riesz vector into the concrete normal
`-J_full X_full(0)`. -/
theorem canonicalCompletedC3FullOperatorCrossingNormal_eq_neg_operator :
    canonicalCompletedC3FullOperatorCrossingNormal =
      -canonicalCompletedC3FullWronskianOperator
        canonicalCompletedC3FullWronskianCentralState := by
  unfold canonicalCompletedC3FullOperatorCrossingNormal
  rw [canonicalCompletedC3FullWronskianOperator_adjoint_eq_neg, neg_apply]

/-- Exact Riesz representation of the cutoff-free crossing functional. -/
theorem canonicalCompletedC3FullOperatorCrossingFunctional_apply_eq_inner_normal
    (v : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullOperatorCrossingFunctional v =
      inner ℂ canonicalCompletedC3FullOperatorCrossingNormal v := by
  unfold canonicalCompletedC3FullOperatorCrossingFunctional
    canonicalCompletedC3FullOperatorCrossingNormal
  change inner ℂ canonicalCompletedC3FullWronskianCentralState
      (canonicalCompletedC3FullWronskianOperator v) = _
  exact
    (canonicalCompletedC3FullWronskianOperator.adjoint_inner_left v
      canonicalCompletedC3FullWronskianCentralState).symm

/-- The null hyperplane of the crossing is exactly the orthogonal complement
of its Riesz normal line. -/
theorem canonicalCompletedC3FullOperatorCrossingFunctional_ker :
  canonicalCompletedC3FullOperatorCrossingFunctional.ker =
      (ℂ ∙ canonicalCompletedC3FullOperatorCrossingNormal)ᗮ := by
  ext v
  rw [LinearMap.mem_ker]
  change canonicalCompletedC3FullOperatorCrossingFunctional v = 0 ↔ _
  rw [
    canonicalCompletedC3FullOperatorCrossingFunctional_apply_eq_inner_normal,
    Submodule.mem_orthogonal_singleton_iff_inner_right]

/-! ## Cutoff-free form of the central crossing theorem -/

/-- The central theorem no longer carries a fictitious cutoff: `h₀` is the
normal component of the unique full real source tangent, divided by the old
ledger normalization. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_crossingNormal_tangent
    :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      inner ℂ canonicalCompletedC3FullOperatorCrossingNormal
          canonicalCompletedC3FullWronskianRealSourceTangent /
        canonicalCompletedC3FullOperatorRealCollisionNormalization 0 := by
  have h :=
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_normalized_symplectic_crossing
      0
  rw [canonicalCompletedC3FullOperatorCentralCrossingFunctional_eq,
    canonicalCompletedC3FullWronskianOperatorRealSourceTangent_eq,
    canonicalCompletedC3FullOperatorCrossingFunctional_apply_eq_inner_normal]
    at h
  exact h

/-- Equivalent unnormalized crossing identity. -/
theorem inner_crossingNormal_realSourceTangent_eq_normalization_mul_h0 :
    inner ℂ canonicalCompletedC3FullOperatorCrossingNormal
        canonicalCompletedC3FullWronskianRealSourceTangent =
      canonicalCompletedC3FullOperatorRealCollisionNormalization 0 *
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  have h :=
    (eq_div_iff
      canonicalCompletedC3FullOperatorRealCollisionNormalization_zero_ne_zero).mp
        canonicalCompletedNativeLogDerivativeMoment_zero_eq_crossingNormal_tangent
  calc
    _ = (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) *
          canonicalCompletedC3FullOperatorRealCollisionNormalization 0 := h.symm
    _ = _ := by ring

/-! ## The normal line is nondegenerate -/

/-- The cutoff-free central state is nonzero already in the value coordinate
of its raw completed boundary trace. -/
theorem canonicalCompletedC3FullWronskianCentralState_ne_zero :
    canonicalCompletedC3FullWronskianCentralState ≠ 0 := by
  intro hzero
  have hcoord := congrArg
    (fun state : CanonicalCompletedC3FullWronskianOperatorCarrier =>
      state.fst.snd) hzero
  have hxi : nativeXiCompletionFactor 0 ≠ 0 :=
    nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain
  have hchart : canonicalC3ChartFactorHeight 0 ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero zero_mem_completedNativeHeightDomain
  have hnative : nativeHeightScalar 0 ≠ 0 := nativeHeightScalar_zero_ne_zero
  apply mul_ne_zero hxi (mul_ne_zero hchart hnative)
  simpa [canonicalCompletedC3FullWronskianCentralState,
    canonicalCompletedC3FullWronskianAnalyticState,
    completedScalarBoundaryTraceState,
    canonicalCompletedC3RawAnalyticValue] using hcoord

/-- The Riesz normal has the same norm as the central state. -/
theorem norm_canonicalCompletedC3FullOperatorCrossingNormal :
    ‖canonicalCompletedC3FullOperatorCrossingNormal‖ =
      ‖canonicalCompletedC3FullWronskianCentralState‖ := by
  rw [canonicalCompletedC3FullOperatorCrossingNormal_eq_neg_operator,
    norm_neg, norm_canonicalCompletedC3FullWronskianOperator]

/-- Hence the normal line has a nonzero generator. -/
theorem canonicalCompletedC3FullOperatorCrossingNormal_ne_zero :
    canonicalCompletedC3FullOperatorCrossingNormal ≠ 0 := by
  intro hzero
  have hnorm := norm_canonicalCompletedC3FullOperatorCrossingNormal
  rw [hzero, norm_zero] at hnorm
  exact canonicalCompletedC3FullWronskianCentralState_ne_zero
    (norm_eq_zero.mp hnorm.symm)

/-! ## Orthogonal projection onto the crossing normal -/

/-- The canonical one-dimensional normal subspace. -/
def canonicalCompletedC3FullOperatorCrossingNormalLine :
    Submodule ℂ CanonicalCompletedC3FullWronskianOperatorCarrier :=
  ℂ ∙ canonicalCompletedC3FullOperatorCrossingNormal

noncomputable local instance canonicalCompletedC3FullOperatorCrossingNormalLineProjection :
    canonicalCompletedC3FullOperatorCrossingNormalLine.HasOrthogonalProjection :=
  { exists_orthogonal := fun v => by
      let coefficient : ℂ :=
        inner ℂ canonicalCompletedC3FullOperatorCrossingNormal v /
          ((‖canonicalCompletedC3FullOperatorCrossingNormal‖ ^ 2 : ℝ) : ℂ)
      refine ⟨coefficient • canonicalCompletedC3FullOperatorCrossingNormal,
        ?_, ?_⟩
      · unfold canonicalCompletedC3FullOperatorCrossingNormalLine
        rw [Submodule.mem_span_singleton]
        exact ⟨coefficient, rfl⟩
      · unfold canonicalCompletedC3FullOperatorCrossingNormalLine
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
          inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
        have hnorm : ‖canonicalCompletedC3FullOperatorCrossingNormal‖ ≠ 0 :=
          norm_ne_zero_iff.mpr
            canonicalCompletedC3FullOperatorCrossingNormal_ne_zero
        dsimp only [coefficient]
        have hcast :
            (((‖canonicalCompletedC3FullOperatorCrossingNormal‖ ^ 2 : ℝ) : ℂ)) =
              ((‖canonicalCompletedC3FullOperatorCrossingNormal‖ : ℂ) ^ 2) := by
          norm_cast
        rw [hcast]
        field_simp [hnorm]
        simp }

/-- Orthogonal projection onto the Riesz normal line; no scale is chosen. -/
def canonicalCompletedC3FullOperatorCrossingNormalProjection :
    CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ]
      CanonicalCompletedC3FullWronskianOperatorCarrier :=
  canonicalCompletedC3FullOperatorCrossingNormalLine.starProjection

theorem canonicalCompletedC3FullOperatorCrossingNormalProjection_apply
    (v : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullOperatorCrossingNormalProjection v =
      (inner ℂ canonicalCompletedC3FullOperatorCrossingNormal v /
          ((‖canonicalCompletedC3FullOperatorCrossingNormal‖ ^ 2 : ℝ) : ℂ)) •
        canonicalCompletedC3FullOperatorCrossingNormal := by
  unfold canonicalCompletedC3FullOperatorCrossingNormalProjection
    canonicalCompletedC3FullOperatorCrossingNormalLine
  rw [Submodule.starProjection_singleton]
  rfl

/-- Squared Hilbert energy of the normal projection of the physical tangent. -/
def canonicalCompletedC3FullOperatorCrossingNormalEnergy : ℝ :=
  ‖canonicalCompletedC3FullOperatorCrossingNormalProjection
      canonicalCompletedC3FullWronskianRealSourceTangent‖ ^ 2

/-- Standard rank-one projection formula for the normal energy. -/
theorem canonicalCompletedC3FullOperatorCrossingNormalEnergy_eq_inner :
    canonicalCompletedC3FullOperatorCrossingNormalEnergy =
      ‖inner ℂ canonicalCompletedC3FullOperatorCrossingNormal
          canonicalCompletedC3FullWronskianRealSourceTangent‖ ^ 2 /
        ‖canonicalCompletedC3FullOperatorCrossingNormal‖ ^ 2 := by
  have hnormalNorm :
      ‖canonicalCompletedC3FullOperatorCrossingNormal‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      canonicalCompletedC3FullOperatorCrossingNormal_ne_zero
  unfold canonicalCompletedC3FullOperatorCrossingNormalEnergy
  rw [canonicalCompletedC3FullOperatorCrossingNormalProjection_apply,
    norm_smul, norm_div, mul_pow, div_pow]
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  field_simp [hnormalNorm]

/-- Closed formula forced by the crossing theorem.  It contains no new
normalization: the only scale is the old ledger denominator. -/
theorem canonicalCompletedC3FullOperatorCrossingNormalEnergy_eq_closed :
    canonicalCompletedC3FullOperatorCrossingNormalEnergy =
      ‖canonicalCompletedC3FullOperatorRealCollisionNormalization 0 *
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)‖ ^ 2 /
        ‖canonicalCompletedC3FullOperatorCrossingNormal‖ ^ 2 := by
  rw [canonicalCompletedC3FullOperatorCrossingNormalEnergy_eq_inner,
    inner_crossingNormal_realSourceTangent_eq_normalization_mul_h0]

/-- Real-scalar expansion of the same formula. -/
theorem canonicalCompletedC3FullOperatorCrossingNormalEnergy_eq_real_closed :
    canonicalCompletedC3FullOperatorCrossingNormalEnergy =
      ‖canonicalCompletedC3FullOperatorRealCollisionNormalization 0‖ ^ 2 *
          canonicalCompletedNativeLogDerivativeMoment 0 ^ 2 /
        ‖canonicalCompletedC3FullOperatorCrossingNormal‖ ^ 2 := by
  rw [canonicalCompletedC3FullOperatorCrossingNormalEnergy_eq_closed,
    norm_mul, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## Exact normal-energy mismatch -/

/-- Projection onto the Riesz normal produces `h₀` exactly only if one
additional scalar normalization identity holds (or `h₀` vanishes).  This is
the first equality not supplied by the linear crossing geometry. -/
theorem canonicalCompletedC3FullOperatorCrossingNormalEnergy_eq_h0_iff :
    canonicalCompletedC3FullOperatorCrossingNormalEnergy =
        canonicalCompletedNativeLogDerivativeMoment 0 ↔
      canonicalCompletedNativeLogDerivativeMoment 0 *
        (‖canonicalCompletedC3FullOperatorRealCollisionNormalization 0‖ ^ 2 *
            canonicalCompletedNativeLogDerivativeMoment 0 -
          ‖canonicalCompletedC3FullOperatorCrossingNormal‖ ^ 2) = 0 := by
  have hnormalSq :
      ‖canonicalCompletedC3FullOperatorCrossingNormal‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr
      canonicalCompletedC3FullOperatorCrossingNormal_ne_zero)
  rw [canonicalCompletedC3FullOperatorCrossingNormalEnergy_eq_real_closed]
  constructor
  · intro h
    have hcross := (div_eq_iff hnormalSq).mp h
    nlinarith
  · intro h
    apply (div_eq_iff hnormalSq).2
    nlinarith

/-- On the nonzero `h₀` branch, the missing condition is the exact scale
identity `||n||² = ||D(0)||² h₀`. -/
theorem canonicalCompletedC3FullOperatorCrossingNormalEnergy_eq_h0_iff_of_ne
    (hzero : canonicalCompletedNativeLogDerivativeMoment 0 ≠ 0) :
    canonicalCompletedC3FullOperatorCrossingNormalEnergy =
        canonicalCompletedNativeLogDerivativeMoment 0 ↔
      ‖canonicalCompletedC3FullOperatorCrossingNormal‖ ^ 2 =
        ‖canonicalCompletedC3FullOperatorRealCollisionNormalization 0‖ ^ 2 *
          canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [canonicalCompletedC3FullOperatorCrossingNormalEnergy_eq_h0_iff]
  constructor
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hzero)
      |>.symm
  · intro h
    apply mul_eq_zero.mpr
    right
    rw [h]
    ring

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeProductNativeClockProjectionAudit
import CarrySelfAdjointOperator.CompletedNativeLocalProductGreenAudit
import CarrySelfAdjointOperator.BR2RadialNormalizedComplexJetNoGo
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
# Clock quotient versus the native Green defect

This file packages the length-three clock removal as the literal orthogonal
projection onto the complement of the clock line.  It then expands the
projected two-point kernel as the forced rank-one Schur correction.

The final section keeps separate two carriers which coincide only after the
center diagonal collapse: the one-leg finite prefix and the original
two-leg C3 port.  This distinction is decisive for the Green audit.
-/

open scoped ComplexConjugate InnerProduct InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## The canonical finite-prefix quotient -/

/-- The clock line in the actual length-three prefix carrier. -/
def canonicalCompletedNativeC3FiniteClockLine :
    Submodule ℂ CarryVerticalL2 :=
  ℂ ∙ canonicalCompletedNativeC3CenterFiniteLogJetState

noncomputable local instance canonicalCompletedNativeC3FiniteClockLineComplete :
    CompleteSpace canonicalCompletedNativeC3FiniteClockLine :=
  letI : FiniteDimensional ℂ canonicalCompletedNativeC3FiniteClockLine :=
    FiniteDimensional.span_of_finite ℂ
      (Set.finite_singleton canonicalCompletedNativeC3CenterFiniteLogJetState)
  FiniteDimensional.complete ℂ canonicalCompletedNativeC3FiniteClockLine

noncomputable local instance canonicalCompletedNativeC3FiniteClockLineProjection :
    canonicalCompletedNativeC3FiniteClockLine.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace
    canonicalCompletedNativeC3FiniteClockLine

/-- `Q₃ = I - P_span(L₃)`, implemented as the orthogonal projection onto
the complement of the clock line. -/
def canonicalCompletedNativeC3FiniteClockQuotient :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  (Submodule.orthogonal canonicalCompletedNativeC3FiniteClockLine).starProjection

theorem canonicalCompletedNativeC3FiniteClockQuotient_eq_id_sub_projection :
    canonicalCompletedNativeC3FiniteClockQuotient =
      ContinuousLinearMap.id ℂ CarryVerticalL2 -
        canonicalCompletedNativeC3FiniteClockLine.starProjection := by
  exact Submodule.starProjection_orthogonal
    canonicalCompletedNativeC3FiniteClockLine

/-- `Q₃² = Q₃`. -/
theorem canonicalCompletedNativeC3FiniteClockQuotient_idempotent :
    canonicalCompletedNativeC3FiniteClockQuotient ∘L
        canonicalCompletedNativeC3FiniteClockQuotient =
      canonicalCompletedNativeC3FiniteClockQuotient := by
  exact (Submodule.orthogonal
    canonicalCompletedNativeC3FiniteClockLine).isIdempotentElem_starProjection

/-- `Q₃* = Q₃`. -/
theorem canonicalCompletedNativeC3FiniteClockQuotient_adjoint :
    canonicalCompletedNativeC3FiniteClockQuotient.adjoint =
      canonicalCompletedNativeC3FiniteClockQuotient := by
  exact (isSelfAdjoint_starProjection
    (Submodule.orthogonal canonicalCompletedNativeC3FiniteClockLine)).adjoint_eq

/-- The quotient kills exactly the clock line. -/
theorem canonicalCompletedNativeC3FiniteClockQuotient_ker :
    canonicalCompletedNativeC3FiniteClockQuotient.ker =
      canonicalCompletedNativeC3FiniteClockLine := by
  simp [canonicalCompletedNativeC3FiniteClockQuotient,
    canonicalCompletedNativeC3FiniteClockLine]

/-- Explicit forced formula for the quotient. -/
theorem canonicalCompletedNativeC3FiniteClockQuotient_apply
    (x : CarryVerticalL2) :
    canonicalCompletedNativeC3FiniteClockQuotient x =
      x -
        (inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetState x /
            ((‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ ^ 2 : ℝ) : ℂ)) •
          canonicalCompletedNativeC3CenterFiniteLogJetState := by
  rw [canonicalCompletedNativeC3FiniteClockQuotient,
    Submodule.starProjection_orthogonal_val]
  change x - (ℂ ∙ canonicalCompletedNativeC3CenterFiniteLogJetState).starProjection x = _
  rw [Submodule.starProjection_singleton]
  rfl

/-- The old residual is literally `Q₃ O₃`. -/
theorem canonicalCompletedNativeC3FiniteClockQuotient_ordinaryState :
    canonicalCompletedNativeC3FiniteClockQuotient
        canonicalCompletedNativeC3CenterFiniteOrdinaryState =
      canonicalCompletedNativeC3CenterFiniteClockResidual := by
  rw [canonicalCompletedNativeC3FiniteClockQuotient_apply]
  unfold canonicalCompletedNativeC3CenterFiniteClockResidual
    canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient
  norm_cast

/-- Orthogonal clock removal is contractive on every vector, not only on
the central ordinary state. -/
theorem norm_canonicalCompletedNativeC3FiniteClockQuotient_le
    (x : CarryVerticalL2) :
    ‖canonicalCompletedNativeC3FiniteClockQuotient x‖ ≤ ‖x‖ := by
  exact (Submodule.orthogonal
    canonicalCompletedNativeC3FiniteClockLine).norm_starProjection_apply_le x

/-! ## The projected one-leg kernel -/

/-- The varying ordinary length-three prefix before the center-only collapse. -/
def canonicalCompletedNativeC3FiniteOrdinaryState (z : ℂ) : CarryVerticalL2 :=
  canonicalCompletedC3DirichletGradientPrefixState
    (operatorHeightParameter z) 3

/-- Raw one-leg kernel.  This is not silently identified with the two-leg
kernel used in `CompletedNativeLocalProductGreenAudit`. -/
def canonicalCompletedNativeC3FiniteRawKernel (w z : ℂ) : ℂ :=
  inner ℂ (canonicalCompletedNativeC3FiniteOrdinaryState w)
    (canonicalCompletedNativeC3FiniteOrdinaryState z)

/-- Rank-one clock term removed from the raw one-leg kernel. -/
def canonicalCompletedNativeC3FiniteClockKernelCorrection (w z : ℂ) : ℂ :=
  inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetState
      (canonicalCompletedNativeC3FiniteOrdinaryState z) *
    inner ℂ (canonicalCompletedNativeC3FiniteOrdinaryState w)
      canonicalCompletedNativeC3CenterFiniteLogJetState /
    ((‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ ^ 2 : ℝ) : ℂ)

/-- Kernel after quotienting by the fixed central clock line. -/
def canonicalCompletedNativeC3FiniteClockQuotientKernel (w z : ℂ) : ℂ :=
  inner ℂ
    (canonicalCompletedNativeC3FiniteClockQuotient
      (canonicalCompletedNativeC3FiniteOrdinaryState w))
    (canonicalCompletedNativeC3FiniteClockQuotient
      (canonicalCompletedNativeC3FiniteOrdinaryState z))

/-- Exact Schur expansion, with Lean's convention (conjugate-linear in the
first slot and linear in the second slot). -/
theorem canonicalCompletedNativeC3FiniteClockQuotientKernel_eq_raw_sub :
    canonicalCompletedNativeC3FiniteClockQuotientKernel =
      fun w z ↦ canonicalCompletedNativeC3FiniteRawKernel w z -
        canonicalCompletedNativeC3FiniteClockKernelCorrection w z := by
  funext w z
  unfold canonicalCompletedNativeC3FiniteClockQuotientKernel
  have hsym := (Submodule.orthogonal
    canonicalCompletedNativeC3FiniteClockLine).inner_starProjection_left_eq_right
      (canonicalCompletedNativeC3FiniteOrdinaryState w)
      (canonicalCompletedNativeC3FiniteClockQuotient
        (canonicalCompletedNativeC3FiniteOrdinaryState z))
  change inner ℂ
      (canonicalCompletedNativeC3FiniteClockQuotient
        (canonicalCompletedNativeC3FiniteOrdinaryState w))
      (canonicalCompletedNativeC3FiniteClockQuotient
        (canonicalCompletedNativeC3FiniteOrdinaryState z)) =
    inner ℂ (canonicalCompletedNativeC3FiniteOrdinaryState w)
      (canonicalCompletedNativeC3FiniteClockQuotient
        (canonicalCompletedNativeC3FiniteClockQuotient
          (canonicalCompletedNativeC3FiniteOrdinaryState z))) at hsym
  have hidem := DFunLike.congr_fun
    canonicalCompletedNativeC3FiniteClockQuotient_idempotent
      (canonicalCompletedNativeC3FiniteOrdinaryState z)
  simp only [ContinuousLinearMap.comp_apply] at hidem
  rw [hidem] at hsym
  rw [hsym, canonicalCompletedNativeC3FiniteClockQuotient_apply,
    inner_sub_right, inner_smul_right]
  unfold canonicalCompletedNativeC3FiniteRawKernel
    canonicalCompletedNativeC3FiniteClockKernelCorrection
  field_simp

/-! ## Canonical central lift to the original two-leg port -/

/-- The existing zero extension, bundled as a complex linear isometry. -/
def finiteC3LegL2ExtensionIsometry (M : ℕ) :
    NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M →ₗᵢ[ℂ]
      CarryVerticalL2 where
  toLinearMap :=
    { toFun := finiteC3LegL2Extension M
      map_add' := finiteC3LegL2Extension_add M
      map_smul' := finiteC3LegL2Extension_smul M }
  norm_map' := norm_finiteC3LegL2Extension M

@[simp] theorem finiteC3LegL2ExtensionIsometry_apply
    (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    finiteC3LegL2ExtensionIsometry M x = finiteC3LegL2Extension M x :=
  rfl

/-- Length-three logarithmic leg before zero extension. -/
def canonicalCompletedNativeC3CenterFiniteLogJetLeg :
    NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3 :=
  WithLp.toLp 2 (fun n : Fin 3 ↦
    positiveLogDirichletGradient (1 / 2 : ℂ) n)

/-- The log leg extends to the already defined `L₃`. -/
theorem finiteC3LegL2Extension_logJetLeg :
    finiteC3LegL2Extension 3
        canonicalCompletedNativeC3CenterFiniteLogJetLeg =
      canonicalCompletedNativeC3CenterFiniteLogJetState := by
  apply lp.ext
  funext n
  rw [finiteC3LegL2Extension_apply]
  by_cases hn : n < 3
  · simp [canonicalCompletedNativeC3CenterFiniteLogJetLeg,
      canonicalCompletedNativeC3CenterFiniteLogJetState,
      canonicalCompletedC3LogJetPrefixState_apply, hn]
  · simp [canonicalCompletedNativeC3CenterFiniteLogJetState,
      canonicalCompletedC3LogJetPrefixState_apply, hn]

/-- The ordinary center leg in the original finite port. -/
def canonicalCompletedNativeC3CenterFiniteOrdinaryLeg :
    NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3 :=
  (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
    (operatorHeightParameter 0)).2

/-- The ordinary center leg extends to `O₃`. -/
theorem finiteC3LegL2Extension_ordinaryLeg :
    finiteC3LegL2Extension 3
        canonicalCompletedNativeC3CenterFiniteOrdinaryLeg =
      canonicalCompletedNativeC3CenterFiniteOrdinaryState := by
  unfold canonicalCompletedNativeC3CenterFiniteOrdinaryLeg
    canonicalCompletedNativeC3CenterFiniteOrdinaryState
  rw [finiteC3GenuineSecondLegL2Extension_eq_prefix]
  congr 1
  norm_num [operatorHeightParameter]

/-- The raw clock direction in the original two-leg port.  Along the real
height line the true tangent is `-i` times this vector, so its span is forced
and contains no adjustable weight. -/
def canonicalCompletedNativeC3CenterClockPortDirection :
    CanonicalCompletedC3HilbertCarrier :=
  WithLp.toLp 2
    (canonicalCompletedNativeC3CenterFiniteLogJetLeg,
      canonicalCompletedNativeC3CenterFiniteLogJetLeg)

/-- The actual real-height tangent in the two-leg port.  Multiplication by
`-i` is forced by differentiating `n^{-s}` along `s = 1/2 + it`. -/
def canonicalCompletedNativeC3CenterClockPortTangent :
    CanonicalCompletedC3HilbertCarrier :=
  (-Complex.I) • canonicalCompletedNativeC3CenterClockPortDirection

/-- On the real height line the phase-normalized first leg loses its radial
factor and is the same ordinary prefix as the second leg. -/
theorem canonicalCompletedOperatorC3HilbertState_ofReal_fst_apply
    (time : ℝ) (n : Fin 3) :
    (WithLp.ofLp
      (canonicalCompletedOperatorC3HilbertState (time : ℂ))).1 n =
      positiveDirichletGradient (nativeLine time) n := by
  unfold canonicalCompletedOperatorC3HilbertState
    canonicalCompletedOperatorC3State
  rw [canonicalEnrichedC3SourcePort_eq_greenBoundaryPair,
    finiteC3GenuineBracketGreenBoundaryPair_fst_eq_radial_mul_completedPrefix]
  simp [operatorHeightParameter, nativeLine, criticalDisplacement,
    canonicalCompletedC3DirichletGradientPrefixState_apply, n.isLt]
  rw [mul_comm Complex.I (time : ℂ)]

/-- The second leg is the same real-height ordinary prefix. -/
theorem canonicalCompletedOperatorC3HilbertState_ofReal_snd_apply
    (time : ℝ) (n : Fin 3) :
    (WithLp.ofLp
      (canonicalCompletedOperatorC3HilbertState (time : ℂ))).2 n =
      positiveDirichletGradient (nativeLine time) n := by
  unfold canonicalCompletedOperatorC3HilbertState
    canonicalCompletedOperatorC3State
  rw [canonicalEnrichedC3SourcePort_eq_greenBoundaryPair,
    finiteC3GenuineBracketGreenBoundaryPair_snd_eq_completedPrefix]
  simp [operatorHeightParameter, nativeLine,
    canonicalCompletedC3DirichletGradientPrefixState_apply, n.isLt]
  rw [mul_comm Complex.I (time : ℂ)]

/-- Coordinatewise on the first original leg, the lifted vector is the true
center tangent along the physical real-height line. -/
theorem hasDerivAt_canonicalCompletedOperatorC3HilbertState_ofReal_fst
    (n : Fin 3) :
    HasDerivAt
      (fun time : ℝ ↦
        (WithLp.ofLp
          (canonicalCompletedOperatorC3HilbertState (time : ℂ))).1 n)
      ((WithLp.ofLp canonicalCompletedNativeC3CenterClockPortTangent).1 n) 0 := by
  have h := hasDerivAt_positiveDirichletGradient_nativeLine (n : ℕ) 0
  rw [show (fun time : ℝ ↦
      (WithLp.ofLp
        (canonicalCompletedOperatorC3HilbertState (time : ℂ))).1 n) =
      fun time : ℝ ↦ positiveDirichletGradient (nativeLine time) n by
        funext time
        exact canonicalCompletedOperatorC3HilbertState_ofReal_fst_apply time n]
  simpa [canonicalCompletedNativeC3CenterClockPortTangent,
    canonicalCompletedNativeC3CenterClockPortDirection,
    canonicalCompletedNativeC3CenterFiniteLogJetLeg, nativeLine] using h

/-- The same forced tangent occurs on the second original leg. -/
theorem hasDerivAt_canonicalCompletedOperatorC3HilbertState_ofReal_snd
    (n : Fin 3) :
    HasDerivAt
      (fun time : ℝ ↦
        (WithLp.ofLp
          (canonicalCompletedOperatorC3HilbertState (time : ℂ))).2 n)
      ((WithLp.ofLp canonicalCompletedNativeC3CenterClockPortTangent).2 n) 0 := by
  have h := hasDerivAt_positiveDirichletGradient_nativeLine (n : ℕ) 0
  rw [show (fun time : ℝ ↦
      (WithLp.ofLp
        (canonicalCompletedOperatorC3HilbertState (time : ℂ))).2 n) =
      fun time : ℝ ↦ positiveDirichletGradient (nativeLine time) n by
        funext time
        exact canonicalCompletedOperatorC3HilbertState_ofReal_snd_apply time n]
  simpa [canonicalCompletedNativeC3CenterClockPortTangent,
    canonicalCompletedNativeC3CenterClockPortDirection,
    canonicalCompletedNativeC3CenterFiniteLogJetLeg, nativeLine] using h

/-- The line generated by the lifted clock tangent in the original carrier. -/
def canonicalCompletedNativeC3CenterClockPortLine :
    Submodule ℂ CanonicalCompletedC3HilbertCarrier :=
  ℂ ∙ canonicalCompletedNativeC3CenterClockPortDirection

/-- Central clock quotient before the diagonal collapse. -/
def canonicalCompletedNativeC3CenterClockPortQuotient :
    CanonicalCompletedC3HilbertCarrier →L[ℂ]
      CanonicalCompletedC3HilbertCarrier :=
  ContinuousLinearMap.id ℂ CanonicalCompletedC3HilbertCarrier -
    ((((‖canonicalCompletedNativeC3CenterClockPortDirection‖ ^ 2 : ℝ) : ℂ))⁻¹) •
      InnerProductSpace.rankOne ℂ
        canonicalCompletedNativeC3CenterClockPortDirection
        canonicalCompletedNativeC3CenterClockPortDirection

theorem canonicalCompletedNativeC3CenterClockPortQuotient_apply
    (x : CanonicalCompletedC3HilbertCarrier) :
    canonicalCompletedNativeC3CenterClockPortQuotient x =
      x -
        (inner ℂ canonicalCompletedNativeC3CenterClockPortDirection x /
          (((‖canonicalCompletedNativeC3CenterClockPortDirection‖ ^ 2 : ℝ) : ℂ))) •
            canonicalCompletedNativeC3CenterClockPortDirection := by
  unfold canonicalCompletedNativeC3CenterClockPortQuotient
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, InnerProductSpace.rankOne_apply]
  module

/-- The two equal port legs reproduce twice the one-leg inner product. -/
theorem inner_clockPortDirection_raw_zero :
    inner ℂ canonicalCompletedNativeC3CenterClockPortDirection
        (canonicalCompletedOperatorC3HilbertState 0) =
      2 * inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetState
        canonicalCompletedNativeC3CenterFiniteOrdinaryState := by
  have hlegs := finiteC3GenuineBracketGreenBoundaryPair_zero_fst_eq_snd
  have hinner := (finiteC3LegL2ExtensionIsometry 3).inner_map_map
    canonicalCompletedNativeC3CenterFiniteLogJetLeg
    canonicalCompletedNativeC3CenterFiniteOrdinaryLeg
  change inner ℂ
      (finiteC3LegL2Extension 3 canonicalCompletedNativeC3CenterFiniteLogJetLeg)
      (finiteC3LegL2Extension 3 canonicalCompletedNativeC3CenterFiniteOrdinaryLeg) =
    _ at hinner
  rw [finiteC3LegL2Extension_logJetLeg,
    finiteC3LegL2Extension_ordinaryLeg] at hinner
  unfold canonicalCompletedNativeC3CenterClockPortDirection
    canonicalCompletedOperatorC3HilbertState canonicalCompletedOperatorC3State
  rw [canonicalEnrichedC3SourcePort_eq_greenBoundaryPair,
    WithLp.prod_inner_apply, hlegs]
  change inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetLeg
      canonicalCompletedNativeC3CenterFiniteOrdinaryLeg +
    inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetLeg
      canonicalCompletedNativeC3CenterFiniteOrdinaryLeg = _
  rw [← hinner]
  ring

/-- The lifted clock direction has twice the one-leg squared norm. -/
theorem norm_sq_clockPortDirection :
    ((‖canonicalCompletedNativeC3CenterClockPortDirection‖ : ℂ) ^ 2) =
      2 * ((‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ : ℂ) ^ 2) := by
  have hinner := (finiteC3LegL2ExtensionIsometry 3).inner_map_map
    canonicalCompletedNativeC3CenterFiniteLogJetLeg
    canonicalCompletedNativeC3CenterFiniteLogJetLeg
  change inner ℂ
      (finiteC3LegL2Extension 3 canonicalCompletedNativeC3CenterFiniteLogJetLeg)
      (finiteC3LegL2Extension 3 canonicalCompletedNativeC3CenterFiniteLogJetLeg) =
    _ at hinner
  rw [finiteC3LegL2Extension_logJetLeg] at hinner
  calc
    ((‖canonicalCompletedNativeC3CenterClockPortDirection‖ : ℂ) ^ 2) =
        inner ℂ canonicalCompletedNativeC3CenterClockPortDirection
          canonicalCompletedNativeC3CenterClockPortDirection := by
            symm
            exact inner_self_eq_norm_sq_to_K
              (𝕜 := ℂ) canonicalCompletedNativeC3CenterClockPortDirection
    _ = inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetLeg
          canonicalCompletedNativeC3CenterFiniteLogJetLeg +
        inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetLeg
          canonicalCompletedNativeC3CenterFiniteLogJetLeg := by
            rw [canonicalCompletedNativeC3CenterClockPortDirection,
              WithLp.prod_inner_apply]
    _ = 2 * inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetState
          canonicalCompletedNativeC3CenterFiniteLogJetState := by
            rw [← hinner]
            ring
    _ = 2 * ((‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ : ℂ) ^ 2) := by
      rw [inner_self_eq_norm_sq_to_K]
      rfl

/-- The lifted direction is genuinely nonzero. -/
theorem canonicalCompletedNativeC3CenterClockPortDirection_ne_zero :
    canonicalCompletedNativeC3CenterClockPortDirection ≠ 0 := by
  intro hzero
  have hcoord := congrArg
    (fun x : CanonicalCompletedC3HilbertCarrier ↦ (WithLp.ofLp x).1 (0 : Fin 3))
    hzero
  apply positiveLogDirichletGradient_half_zero_ne_zero
  simpa [canonicalCompletedNativeC3CenterClockPortDirection,
    canonicalCompletedNativeC3CenterFiniteLogJetLeg] using hcoord

theorem norm_sq_clockPortDirection_ne_zero :
    (((‖canonicalCompletedNativeC3CenterClockPortDirection‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
  norm_cast
  exact pow_ne_zero 2
    (norm_ne_zero_iff.mpr
      canonicalCompletedNativeC3CenterClockPortDirection_ne_zero)

/-- The explicit rank-one quotient is orthogonal to the lifted clock line. -/
theorem inner_clockPortDirection_clockPortQuotient_eq_zero
    (x : CanonicalCompletedC3HilbertCarrier) :
    inner ℂ canonicalCompletedNativeC3CenterClockPortDirection
      (canonicalCompletedNativeC3CenterClockPortQuotient x) = 0 := by
  have hself :
      inner ℂ canonicalCompletedNativeC3CenterClockPortDirection
          canonicalCompletedNativeC3CenterClockPortDirection =
        (((‖canonicalCompletedNativeC3CenterClockPortDirection‖ ^ 2 : ℝ) : ℂ)) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hdenom :
      ((‖canonicalCompletedNativeC3CenterClockPortDirection‖ : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2
      (norm_ne_zero_iff.mpr
        canonicalCompletedNativeC3CenterClockPortDirection_ne_zero))
  rw [canonicalCompletedNativeC3CenterClockPortQuotient_apply,
    inner_sub_right, inner_smul_right, hself]
  field_simp [hdenom]
  simp

/-- Thus the lifted quotient is itself idempotent. -/
theorem canonicalCompletedNativeC3CenterClockPortQuotient_idempotent :
    canonicalCompletedNativeC3CenterClockPortQuotient ∘L
        canonicalCompletedNativeC3CenterClockPortQuotient =
      canonicalCompletedNativeC3CenterClockPortQuotient := by
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  rw [canonicalCompletedNativeC3CenterClockPortQuotient_apply,
    inner_clockPortDirection_clockPortQuotient_eq_zero]
  simp

/-- The lifted quotient is self-adjoint as the identity minus a real scalar
multiple of `rankOne(T,T)`. -/
theorem canonicalCompletedNativeC3CenterClockPortQuotient_adjoint :
    canonicalCompletedNativeC3CenterClockPortQuotient.adjoint =
      canonicalCompletedNativeC3CenterClockPortQuotient := by
  unfold canonicalCompletedNativeC3CenterClockPortQuotient
  simp only [map_sub, ContinuousLinearMap.adjoint_id]
  rw [map_smulₛₗ]
  simp

/-- It kills exactly the lifted clock line. -/
theorem canonicalCompletedNativeC3CenterClockPortQuotient_ker :
    canonicalCompletedNativeC3CenterClockPortQuotient.ker =
      canonicalCompletedNativeC3CenterClockPortLine := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    change canonicalCompletedNativeC3CenterClockPortQuotient x = 0 at hx
    have hformula := canonicalCompletedNativeC3CenterClockPortQuotient_apply x
    rw [hx] at hformula
    rw [canonicalCompletedNativeC3CenterClockPortLine,
      Submodule.mem_span_singleton]
    refine ⟨inner ℂ canonicalCompletedNativeC3CenterClockPortDirection x /
      (((‖canonicalCompletedNativeC3CenterClockPortDirection‖ ^ 2 : ℝ) : ℂ)), ?_⟩
    exact (sub_eq_zero.mp hformula.symm).symm
  · rw [canonicalCompletedNativeC3CenterClockPortLine,
      Submodule.mem_span_singleton]
    rintro ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    change canonicalCompletedNativeC3CenterClockPortQuotient
      (c • canonicalCompletedNativeC3CenterClockPortDirection) = 0
    have hself :
        inner ℂ canonicalCompletedNativeC3CenterClockPortDirection
            canonicalCompletedNativeC3CenterClockPortDirection =
          (((‖canonicalCompletedNativeC3CenterClockPortDirection‖ ^ 2 : ℝ) : ℂ)) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hdenom :
        ((‖canonicalCompletedNativeC3CenterClockPortDirection‖ : ℂ) ^ 2) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2
        (norm_ne_zero_iff.mpr
          canonicalCompletedNativeC3CenterClockPortDirection_ne_zero))
    rw [canonicalCompletedNativeC3CenterClockPortQuotient_apply,
      inner_smul_right, hself]
    field_simp [hdenom]
    simp

/-- The projection coefficient in the original two-leg carrier is exactly
the same Hilbert-forced coefficient `c₃`; duplication cancels from numerator
and denominator. -/
theorem clockPort_projectionCoefficient_eq_finite :
    inner ℂ canonicalCompletedNativeC3CenterClockPortDirection
        (canonicalCompletedOperatorC3HilbertState 0) /
        ((‖canonicalCompletedNativeC3CenterClockPortDirection‖ : ℂ) ^ 2) =
      canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient := by
  have hnorm :
      (‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr
      canonicalCompletedNativeC3CenterFiniteLogJetState_ne_zero)
  rw [inner_clockPortDirection_raw_zero, norm_sq_clockPortDirection]
  unfold canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient
  field_simp [hnorm]

theorem clockPort_projectionCoefficient_realDenom_eq_finite :
    inner ℂ canonicalCompletedNativeC3CenterClockPortDirection
        (canonicalCompletedOperatorC3HilbertState 0) /
        (((‖canonicalCompletedNativeC3CenterClockPortDirection‖ ^ 2 : ℝ) : ℂ)) =
      canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient := by
  rw [show (((‖canonicalCompletedNativeC3CenterClockPortDirection‖ ^ 2 : ℝ) : ℂ)) =
      ((‖canonicalCompletedNativeC3CenterClockPortDirection‖ : ℂ) ^ 2) by
        norm_cast]
  exact clockPort_projectionCoefficient_eq_finite

/-- Before collapse the quotient subtracts exactly `c₃` times the lifted
clock direction. -/
theorem canonicalCompletedNativeC3CenterClockPortQuotient_raw_zero :
    canonicalCompletedNativeC3CenterClockPortQuotient
        (canonicalCompletedOperatorC3HilbertState 0) =
      canonicalCompletedOperatorC3HilbertState 0 -
        canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient •
          canonicalCompletedNativeC3CenterClockPortDirection := by
  rw [canonicalCompletedNativeC3CenterClockPortQuotient_apply,
    clockPort_projectionCoefficient_realDenom_eq_finite]

/-- The center collapse is additive. -/
theorem canonicalCompletedC3CenterFiniteDiagonalCollapse_add
    (x y : CanonicalCompletedC3HilbertCarrier) :
    canonicalCompletedC3CenterFiniteDiagonalCollapse (x + y) =
      canonicalCompletedC3CenterFiniteDiagonalCollapse x +
        canonicalCompletedC3CenterFiniteDiagonalCollapse y := by
  unfold canonicalCompletedC3CenterFiniteDiagonalCollapse
  change ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) •
      (finiteC3LegL2Extension 3 ((WithLp.ofLp x).1 + (WithLp.ofLp y).1) +
        finiteC3LegL2Extension 3 ((WithLp.ofLp x).2 + (WithLp.ofLp y).2)) = _
  rw [finiteC3LegL2Extension_add, finiteC3LegL2Extension_add]
  module

/-- Hence it also preserves subtraction. -/
theorem canonicalCompletedC3CenterFiniteDiagonalCollapse_sub
    (x y : CanonicalCompletedC3HilbertCarrier) :
    canonicalCompletedC3CenterFiniteDiagonalCollapse (x - y) =
      canonicalCompletedC3CenterFiniteDiagonalCollapse x -
        canonicalCompletedC3CenterFiniteDiagonalCollapse y := by
  rw [sub_eq_add_neg, canonicalCompletedC3CenterFiniteDiagonalCollapse_add,
    show -y = (-1 : ℂ) • y by simp,
    canonicalCompletedC3CenterFiniteDiagonalCollapse_smul]
  simp [sub_eq_add_neg]

/-- The lifted raw clock direction collapses to `sqrt 2 L₃`. -/
theorem canonicalCompletedC3CenterFiniteDiagonalCollapse_clockPortDirection :
    canonicalCompletedC3CenterFiniteDiagonalCollapse
        canonicalCompletedNativeC3CenterClockPortDirection =
      (((Real.sqrt 2 : ℝ) : ℂ)) •
        canonicalCompletedNativeC3CenterFiniteLogJetState := by
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  unfold canonicalCompletedC3CenterFiniteDiagonalCollapse
    canonicalCompletedNativeC3CenterClockPortDirection
  rw [finiteC3LegL2Extension_logJetLeg, ← two_smul ℂ, smul_smul]
  congr 1
  have hsqrtSq :
      (((Real.sqrt 2 : ℝ) : ℂ)) * (((Real.sqrt 2 : ℝ) : ℂ)) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * 2 =
        (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ *
        ((((Real.sqrt 2 : ℝ) : ℂ)) *
          (((Real.sqrt 2 : ℝ) : ℂ))) := by rw [hsqrtSq]
    _ = (((Real.sqrt 2 : ℝ) : ℂ)) := by field_simp [hsqrt]

/-- Quotienting in the original carrier and then collapsing gives exactly
`sqrt 2 R₃` at the raw center. -/
theorem canonicalCompletedC3CenterFiniteDiagonalCollapse_portQuotient_raw_zero :
    canonicalCompletedC3CenterFiniteDiagonalCollapse
        (canonicalCompletedNativeC3CenterClockPortQuotient
          (canonicalCompletedOperatorC3HilbertState 0)) =
      (((Real.sqrt 2 : ℝ) : ℂ)) •
        canonicalCompletedNativeC3CenterFiniteClockResidual := by
  rw [canonicalCompletedNativeC3CenterClockPortQuotient_raw_zero,
    canonicalCompletedC3CenterFiniteDiagonalCollapse_sub,
    canonicalCompletedC3CenterFiniteDiagonalCollapse_raw_zero,
    canonicalCompletedC3CenterFiniteDiagonalCollapse_smul,
    canonicalCompletedC3CenterFiniteDiagonalCollapse_clockPortDirection]
  unfold canonicalCompletedNativeC3CenterFiniteClockResidual
  module

/-- The same statement for the normalized native coordinate `g₀`. -/
theorem canonicalCompletedC3CenterFiniteDiagonalCollapse_portQuotient_g0 :
    canonicalCompletedC3CenterFiniteDiagonalCollapse
        (canonicalCompletedNativeC3CenterClockPortQuotient
          (normalizedCompletedGreenState nativeHeightScalar
            canonicalCompletedOperatorC3HilbertState 0)) =
      (nativeHeightScalar 0)⁻¹ •
        canonicalCompletedNativeC3CenterFiniteClockResidual := by
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  have hG : nativeHeightScalar 0 ≠ 0 := nativeHeightScalar_zero_ne_zero
  unfold normalizedCompletedGreenState
  rw [map_smul, canonicalCompletedC3CenterFiniteDiagonalCollapse_smul,
    canonicalCompletedC3CenterFiniteDiagonalCollapse_portQuotient_raw_zero,
    smul_smul]
  congr 1
  field_simp [hsqrt, hG]

/-! ## The quotient kernel in the original two-leg carrier -/

/-- This is exactly the raw native kernel used in the local Green audit. -/
def canonicalCompletedNativeC3ClockPortRawKernel (w z : ℂ) : ℂ :=
  inner ℂ (canonicalCompletedOperatorC3HilbertState w)
    (canonicalCompletedOperatorC3HilbertState z)

/-- Rank-one term removed by the lifted clock quotient. -/
def canonicalCompletedNativeC3ClockPortKernelCorrection (w z : ℂ) : ℂ :=
  inner ℂ canonicalCompletedNativeC3CenterClockPortDirection
      (canonicalCompletedOperatorC3HilbertState z) *
    inner ℂ (canonicalCompletedOperatorC3HilbertState w)
      canonicalCompletedNativeC3CenterClockPortDirection /
    (((‖canonicalCompletedNativeC3CenterClockPortDirection‖ ^ 2 : ℝ) : ℂ))

/-- Kernel after quotienting the original two-leg state. -/
def canonicalCompletedNativeC3ClockPortQuotientKernel (w z : ℂ) : ℂ :=
  inner ℂ
    (canonicalCompletedNativeC3CenterClockPortQuotient
      (canonicalCompletedOperatorC3HilbertState w))
    (canonicalCompletedNativeC3CenterClockPortQuotient
      (canonicalCompletedOperatorC3HilbertState z))

/-- Exact two-leg Schur expansion. -/
theorem canonicalCompletedNativeC3ClockPortQuotientKernel_eq_raw_sub :
    canonicalCompletedNativeC3ClockPortQuotientKernel =
      fun w z ↦ canonicalCompletedNativeC3ClockPortRawKernel w z -
        canonicalCompletedNativeC3ClockPortKernelCorrection w z := by
  funext w z
  have hsym := ContinuousLinearMap.adjoint_inner_right
    canonicalCompletedNativeC3CenterClockPortQuotient
    (canonicalCompletedOperatorC3HilbertState w)
    (canonicalCompletedNativeC3CenterClockPortQuotient
      (canonicalCompletedOperatorC3HilbertState z))
  rw [canonicalCompletedNativeC3CenterClockPortQuotient_adjoint] at hsym
  have hidem := DFunLike.congr_fun
    canonicalCompletedNativeC3CenterClockPortQuotient_idempotent
      (canonicalCompletedOperatorC3HilbertState z)
  simp only [ContinuousLinearMap.comp_apply] at hidem
  rw [hidem] at hsym
  unfold canonicalCompletedNativeC3ClockPortQuotientKernel
  rw [← hsym, canonicalCompletedNativeC3CenterClockPortQuotient_apply,
    inner_sub_right, inner_smul_right]
  unfold canonicalCompletedNativeC3ClockPortRawKernel
    canonicalCompletedNativeC3ClockPortKernelCorrection
  field_simp

/-! ## What a Green identification would have to prove -/

/-- The actual two-leg raw Green defect from the carrier used in `da09c10`. -/
def canonicalCompletedNativeC3ClockPortRawGreenDefect (z w : ℂ) : ℂ :=
  completedGreenWronskian
      nativeHeightScalar nativeHeightScalarBoundaryCompanion z w -
    (z - (starRingEnd ℂ) w) *
      canonicalCompletedNativeC3ClockPortRawKernel w z

/-- On the original carrier, exact compensation by the clock quotient is
equivalent to this concrete rank-one defect identity. -/
theorem canonicalCompletedNativeC3ClockPortQuotient_green_iff_defect :
    HasDivisionFreeGreenRepresentationOn
        completedNativeHeightDomain
        nativeHeightScalar nativeHeightScalarBoundaryCompanion
        (fun z ↦ canonicalCompletedNativeC3CenterClockPortQuotient
          (canonicalCompletedOperatorC3HilbertState z)) ↔
      ∀ z ∈ completedNativeHeightDomain,
        ∀ w ∈ completedNativeHeightDomain,
          canonicalCompletedNativeC3ClockPortRawGreenDefect z w =
            -(z - (starRingEnd ℂ) w) *
              canonicalCompletedNativeC3ClockPortKernelCorrection w z := by
  constructor <;> intro h z hz w hw
  · have hzw := h z hz w hw
    have hkernel := congrFun
      (congrFun canonicalCompletedNativeC3ClockPortQuotientKernel_eq_raw_sub w) z
    unfold canonicalCompletedNativeC3ClockPortRawGreenDefect
    change completedGreenWronskian nativeHeightScalar
        nativeHeightScalarBoundaryCompanion z w =
      (z - (starRingEnd ℂ) w) *
        canonicalCompletedNativeC3ClockPortQuotientKernel w z at hzw
    rw [hkernel] at hzw
    rw [hzw]
    ring
  · have hzw := h z hz w hw
    have hkernel := congrFun
      (congrFun canonicalCompletedNativeC3ClockPortQuotientKernel_eq_raw_sub w) z
    unfold canonicalCompletedNativeC3ClockPortRawGreenDefect at hzw
    change completedGreenWronskian nativeHeightScalar
        nativeHeightScalarBoundaryCompanion z w =
      (z - (starRingEnd ℂ) w) *
        canonicalCompletedNativeC3ClockPortQuotientKernel w z
    rw [hkernel]
    linear_combination hzw

/-- At the center the actual two-leg defect is the native Wronskian itself;
the kernel, projected or not, is killed by the collision multiplier. -/
theorem canonicalCompletedNativeC3ClockPortRawGreenDefect_zero_zero :
    canonicalCompletedNativeC3ClockPortRawGreenDefect 0 0 =
      completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 := by
  simp [canonicalCompletedNativeC3ClockPortRawGreenDefect]

/-- The lifted clock correction vanishes after multiplication by the Green
factor at the collision center. -/
theorem canonicalCompletedNativeC3ClockPortCorrection_center_collision :
    ((0 : ℂ) - (starRingEnd ℂ) 0) *
      canonicalCompletedNativeC3ClockPortKernelCorrection 0 0 = 0 := by
  simp

/-- Therefore even the quotient on the correct original carrier still
forces the zeroth native Wronskian to vanish. -/
theorem canonicalCompletedNativeC3ClockPortQuotient_green_implies_centerWronskian_zero
    (hgreen : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
      (fun z ↦ canonicalCompletedNativeC3CenterClockPortQuotient
        (canonicalCompletedOperatorC3HilbertState z))) :
    completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 = 0 := by
  simpa using hgreen 0 zero_mem_completedNativeHeightDomain
    0 zero_mem_completedNativeHeightDomain

/-- The collision obstruction is exactly the same upstream scalar equality
as before: a Green identity for the clock quotient would force `G'(0)=0`. -/
theorem canonicalCompletedNativeC3ClockPortQuotient_green_implies_deriv_zero
    (hgreen : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
      (fun z ↦ canonicalCompletedNativeC3CenterClockPortQuotient
        (canonicalCompletedOperatorC3HilbertState z))) :
    deriv nativeHeightScalar 0 = 0 := by
  have hwronskian :=
    canonicalCompletedNativeC3ClockPortQuotient_green_implies_centerWronskian_zero
      hgreen
  have hvalue : nativeHeightScalar 0 ≠ 0 := nativeHeightScalar_zero_ne_zero
  have hproduct : nativeHeightScalar 0 * deriv nativeHeightScalar 0 = 0 := by
    calc
      nativeHeightScalar 0 * deriv nativeHeightScalar 0 =
          -(1 / 2 : ℂ) *
            completedGreenWronskian
              nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 := by
        unfold completedGreenWronskian nativeHeightScalarBoundaryCompanion
        rw [nativeHeightScalar_zero_conj,
          map_neg, nativeHeightScalar_deriv_zero_conj]
        ring
      _ = 0 := by rw [hwronskian]; ring
  exact (mul_eq_zero.mp hproduct).resolve_left hvalue

/-- Defect of the one-leg raw kernel against the concrete native Wronskian.
This is deliberately not the two-leg defect from `da09c10`. -/
def canonicalCompletedNativeC3FiniteRawGreenDefect (z w : ℂ) : ℂ :=
  completedGreenWronskian
      nativeHeightScalar nativeHeightScalarBoundaryCompanion z w -
    (z - (starRingEnd ℂ) w) *
      canonicalCompletedNativeC3FiniteRawKernel w z

/-- The quotient is a division-free Green representation exactly when the
raw defect is the negative clock correction times the Green multiplier. -/
theorem canonicalCompletedNativeC3FiniteClockQuotient_green_iff_defect :
    HasDivisionFreeGreenRepresentationOn
        completedNativeHeightDomain
        nativeHeightScalar nativeHeightScalarBoundaryCompanion
        (fun z ↦ canonicalCompletedNativeC3FiniteClockQuotient
          (canonicalCompletedNativeC3FiniteOrdinaryState z)) ↔
      ∀ z ∈ completedNativeHeightDomain,
        ∀ w ∈ completedNativeHeightDomain,
          canonicalCompletedNativeC3FiniteRawGreenDefect z w =
            -(z - (starRingEnd ℂ) w) *
              canonicalCompletedNativeC3FiniteClockKernelCorrection w z := by
  constructor <;> intro h z hz w hw
  · have hzw := h z hz w hw
    have hkernel := congrFun
      (congrFun canonicalCompletedNativeC3FiniteClockQuotientKernel_eq_raw_sub w) z
    unfold canonicalCompletedNativeC3FiniteRawGreenDefect
    change completedGreenWronskian nativeHeightScalar
        nativeHeightScalarBoundaryCompanion z w =
      (z - (starRingEnd ℂ) w) *
        canonicalCompletedNativeC3FiniteClockQuotientKernel w z at hzw
    rw [hkernel] at hzw
    rw [hzw]
    ring
  · have hzw := h z hz w hw
    have hkernel := congrFun
      (congrFun canonicalCompletedNativeC3FiniteClockQuotientKernel_eq_raw_sub w) z
    unfold canonicalCompletedNativeC3FiniteRawGreenDefect at hzw
    change completedGreenWronskian nativeHeightScalar
        nativeHeightScalarBoundaryCompanion z w =
      (z - (starRingEnd ℂ) w) *
        canonicalCompletedNativeC3FiniteClockQuotientKernel w z
    rw [hkernel]
    linear_combination hzw

/-- At the collision center every fixed kernel correction is annihilated by
the Green multiplier.  Therefore clock projection cannot repair a nonzero
zeroth-diagonal native Wronskian. -/
theorem canonicalCompletedNativeC3FiniteClockCorrection_center_collision :
    ((0 : ℂ) - (starRingEnd ℂ) 0) *
      canonicalCompletedNativeC3FiniteClockKernelCorrection 0 0 = 0 := by
  simp

/-- Consequently the projected Green identity still forces the same center
Wronskian obstruction isolated in `da09c10`. -/
theorem canonicalCompletedNativeC3FiniteClockQuotient_green_implies_centerWronskian_zero
    (hgreen : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
      (fun z ↦ canonicalCompletedNativeC3FiniteClockQuotient
        (canonicalCompletedNativeC3FiniteOrdinaryState z))) :
    completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 = 0 := by
  simpa using hgreen 0 zero_mem_completedNativeHeightDomain
    0 zero_mem_completedNativeHeightDomain

/-! ## Why the central tangent does not give an off-diagonal complex jet -/

/-- The raw original two-leg state has the same radial-phase obstruction as
the normalized product ledger: its first retained coordinate is a nonzero
holomorphic factor times `exp (log 3 * im z)`.  Thus the real-axis clock
tangent constructed above has no canonical complex derivative extension at
the center. -/
theorem canonicalCompletedOperatorC3HilbertState_not_differentiableAt_zero :
    ¬ DifferentiableAt ℂ canonicalCompletedOperatorC3HilbertState 0 := by
  intro hstate
  have hreadout : DifferentiableAt ℂ
      (fun z : ℂ ↦ canonicalCompletedC3FirstZeroReadout
        (canonicalCompletedOperatorC3HilbertState z)) 0 :=
    canonicalCompletedC3FirstZeroReadout.differentiableAt.comp 0 hstate
  let holomorphicFactor : ℂ → ℂ := fun z ↦
    positiveDirichletGradient (operatorHeightParameter z) 0
  have hfactor : DifferentiableAt ℂ holomorphicFactor 0 := by
    exact positiveDirichletGradient_operatorHeight_differentiableAt_zero
  have hfactorZero : holomorphicFactor 0 ≠ 0 := by
    exact positiveDirichletGradient_operatorHeight_zero_ne_zero
  have hproduct : DifferentiableAt ℂ
      (fun z : ℂ ↦ br2RadialPhase z * holomorphicFactor z) 0 := by
    apply hreadout.congr_of_eventuallyEq
    filter_upwards with z
    rw [canonicalCompletedC3FirstZeroReadout_state,
      phaseNormalizedC3Gradient_operatorHeight_eq_radialPhase_mul]
  have hquotient : DifferentiableAt ℂ
      (fun z : ℂ ↦
        (br2RadialPhase z * holomorphicFactor z) / holomorphicFactor z) 0 :=
    hproduct.div hfactor hfactorZero
  have hfactorEventually : ∀ᶠ z in nhds (0 : ℂ), holomorphicFactor z ≠ 0 :=
    hfactor.continuousAt.eventually_ne hfactorZero
  have hradial : DifferentiableAt ℂ br2RadialPhase 0 := by
    apply hquotient.congr_of_eventuallyEq
    filter_upwards [hfactorEventually] with z hz
    exact (mul_div_cancel_right₀ (br2RadialPhase z) hz).symm
  exact br2RadialPhase_not_differentiableAt_complex hradial

end

end CarrySelfAdjointOperator

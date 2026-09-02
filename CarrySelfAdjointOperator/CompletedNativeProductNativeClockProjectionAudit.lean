import CarrySelfAdjointOperator.CompletedNativeProductNativeCoordinateSanityAudit
import CarrySelfAdjointOperator.CompletedC3AmbientRadialTiltSamplePositivity
import CarrySelfAdjointOperator.CompletedC3SymplecticNaimarkVectorLimit
import CarrySelfAdjointOperator.CompletedC3ConcreteDressedLowOrderAudit
import Mathlib.Tactic

/-!
# Clock projection audit for the native product coordinate

The native coordinate in the product ledger is a normalized finite C3 port,
whereas the previously defined central clock Schur energy uses the completed
all-cutoff ordinary and logarithmic states in `CarryVerticalL2`.

This file records the exact bridge supplied by the existing zero-extension
map.  At the center the two finite C3 legs coincide, and their symmetric
diagonal collapse is exactly the native-normalized ordinary prefix of length
three.  It is not the all-cutoff ordinary state: the first omitted coordinate
is already nonzero.

The file then performs the canonical clock quotient on that same finite
prefix.  The projection coefficient is forced by the Hilbert inner product;
no fitted scalar is introduced.
-/

open scoped ComplexConjugate InnerProductSpace BigOperators lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## The finite prefix carried by `g₀` -/

/-- Ordinary length-three prefix obtained from the actual finite C3 port. -/
def canonicalCompletedNativeC3CenterFiniteOrdinaryState : CarryVerticalL2 :=
  canonicalCompletedC3DirichletGradientPrefixState (1 / 2 : ℂ) 3

/-- The corresponding length-three logarithmic clock jet. -/
def canonicalCompletedNativeC3CenterFiniteLogJetState : CarryVerticalL2 :=
  canonicalCompletedC3LogJetPrefixState (1 / 2 : ℂ) 3

/-- Real-height clock tangent of the same finite prefix. -/
def canonicalCompletedNativeC3CenterFiniteClockTangent : CarryVerticalL2 :=
  (-Complex.I) • canonicalCompletedNativeC3CenterFiniteLogJetState

/-- Coordinatewise, the finite clock tangent is forced by differentiating
the ordinary prefix along the native real-height line.  This specializes the
existing low-order derivative theorem; it does not introduce a clock weight. -/
theorem hasDerivAt_canonicalCompletedNativeC3CenterFiniteOrdinaryCoordinate
    (n : ℕ) :
    HasDerivAt
      (fun time : ℝ ↦
        canonicalCompletedC3DirichletGradientPrefixState
          (nativeLine time) 3 n)
      (canonicalCompletedNativeC3CenterFiniteClockTangent n) 0 := by
  by_cases hn : n < 3
  · simpa [canonicalCompletedNativeC3CenterFiniteClockTangent,
      canonicalCompletedNativeC3CenterFiniteLogJetState,
      canonicalCompletedC3DirichletGradientPrefixState_apply,
      canonicalCompletedC3LogJetPrefixState_apply, nativeLine, hn] using
        (hasDerivAt_positiveDirichletGradient_nativeLine n 0)
  · have hconst : HasDerivAt (fun _ : ℝ ↦ (0 : ℂ)) 0 0 :=
      hasDerivAt_const (x := 0) (c := (0 : ℂ))
    simpa [canonicalCompletedNativeC3CenterFiniteClockTangent,
      canonicalCompletedNativeC3CenterFiniteLogJetState,
      canonicalCompletedC3DirichletGradientPrefixState_apply,
      canonicalCompletedC3LogJetPrefixState_apply, hn] using hconst

/-- Zero extension is complex linear.  The existing construction was named
as a function; this is the exact scalar compatibility needed below. -/
theorem finiteC3LegL2Extension_smul
    (M : ℕ) (c : ℂ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    finiteC3LegL2Extension M (c • x) =
      c • finiteC3LegL2Extension M x := by
  apply lp.ext
  funext n
  rw [finiteC3LegL2Extension_apply]
  change (if h : n < M then c * x ⟨n, h⟩ else 0) =
    c * finiteC3LegL2Extension M x n
  rw [finiteC3LegL2Extension_apply]
  by_cases hn : n < M <;> simp [hn]

/-- Zero extension is additive. -/
theorem finiteC3LegL2Extension_add
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    finiteC3LegL2Extension M (x + y) =
      finiteC3LegL2Extension M x + finiteC3LegL2Extension M y := by
  apply lp.ext
  funext n
  rw [finiteC3LegL2Extension_apply]
  change (if h : n < M then x ⟨n, h⟩ + y ⟨n, h⟩ else 0) =
    finiteC3LegL2Extension M x n + finiteC3LegL2Extension M y n
  rw [finiteC3LegL2Extension_apply, finiteC3LegL2Extension_apply]
  by_cases hn : n < M <;> simp [hn]

/-- Zero extension preserves the finite-leg norm. -/
theorem norm_finiteC3LegL2Extension
    (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    ‖finiteC3LegL2Extension M x‖ = ‖x‖ := by
  calc
    ‖finiteC3LegL2Extension M x‖ =
        ‖completedC3GlobalLegCameraIsometry
          (finiteC3LegL2Extension M x)‖ := by
            rw [completedC3GlobalLegCameraIsometry.norm_map]
    _ = ‖finiteC3LegCameraIsometry M x‖ := by
      rw [completedC3GlobalLegCameraIsometry_finiteExtension]
    _ = ‖x‖ := by rw [(finiteC3LegCameraIsometry M).norm_map]

/-- Symmetric diagonal readout from the two-leg finite port into the common
`ell^2` carrier.  The coefficient `1 / sqrt 2` is the canonical coisometric
normalization of the diagonal, not a fitted weight. -/
def canonicalCompletedC3CenterFiniteDiagonalCollapse
    (x : CanonicalCompletedC3HilbertCarrier) : CarryVerticalL2 :=
  ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) •
    (finiteC3LegL2Extension 3 (WithLp.ofLp x).1 +
      finiteC3LegL2Extension 3 (WithLp.ofLp x).2)

/-- The diagonal collapse is complex homogeneous. -/
theorem canonicalCompletedC3CenterFiniteDiagonalCollapse_smul
    (c : ℂ) (x : CanonicalCompletedC3HilbertCarrier) :
    canonicalCompletedC3CenterFiniteDiagonalCollapse (c • x) =
      c • canonicalCompletedC3CenterFiniteDiagonalCollapse x := by
  unfold canonicalCompletedC3CenterFiniteDiagonalCollapse
  change ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) •
      (finiteC3LegL2Extension 3 (c • (WithLp.ofLp x).1) +
        finiteC3LegL2Extension 3 (c • (WithLp.ofLp x).2)) = _
  rw [finiteC3LegL2Extension_smul, finiteC3LegL2Extension_smul,
    ← smul_add]
  module

/-- Before scalar normalization, the centered finite C3 port collapses to
`sqrt 2` times its ordinary length-three prefix. -/
theorem canonicalCompletedC3CenterFiniteDiagonalCollapse_raw_zero :
    canonicalCompletedC3CenterFiniteDiagonalCollapse
        (canonicalCompletedOperatorC3HilbertState 0) =
      (((Real.sqrt 2 : ℝ) : ℂ)) •
        canonicalCompletedNativeC3CenterFiniteOrdinaryState := by
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  have hlegs := finiteC3GenuineBracketGreenBoundaryPair_zero_fst_eq_snd
  unfold canonicalCompletedC3CenterFiniteDiagonalCollapse
    canonicalCompletedOperatorC3HilbertState
    canonicalCompletedNativeC3CenterFiniteOrdinaryState
    canonicalCompletedOperatorC3State
  rw [canonicalEnrichedC3SourcePort_eq_greenBoundaryPair, hlegs,
    finiteC3GenuineSecondLegL2Extension_eq_prefix]
  norm_num [operatorHeightParameter]
  rw [← two_smul ℂ, smul_smul]
  congr 1
  have hsqrtSq :
      (((Real.sqrt 2 : ℝ) : ℂ)) * (((Real.sqrt 2 : ℝ) : ℂ)) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc
    2 * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ =
        (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * 2 := by ring
    _ =
        (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ *
          ((((Real.sqrt 2 : ℝ) : ℂ)) *
            (((Real.sqrt 2 : ℝ) : ℂ))) := by rw [hsqrtSq]
    _ = (((Real.sqrt 2 : ℝ) : ℂ)) := by field_simp [hsqrt]

/-- Smallest vector bridge from `g₀` to the clock carrier: after the
canonical diagonal collapse, `g₀` is exactly the ordinary finite prefix
normalized by the native scalar `G(0)`. -/
theorem canonicalCompletedC3CenterFiniteDiagonalCollapse_g0 :
    canonicalCompletedC3CenterFiniteDiagonalCollapse
        (normalizedCompletedGreenState
          nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0) =
      (nativeHeightScalar 0)⁻¹ •
        canonicalCompletedNativeC3CenterFiniteOrdinaryState := by
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  have hG : nativeHeightScalar 0 ≠ 0 := nativeHeightScalar_zero_ne_zero
  unfold normalizedCompletedGreenState
  rw [canonicalCompletedC3CenterFiniteDiagonalCollapse_smul,
    canonicalCompletedC3CenterFiniteDiagonalCollapse_raw_zero, smul_smul]
  congr 1
  field_simp [hsqrt, hG]

/-- The ordinary finite prefix has exactly the unnormalized one-leg energy
already computed in the center sanity audit. -/
theorem norm_sq_canonicalCompletedNativeC3CenterFiniteOrdinaryState :
    ‖canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 =
      ‖(NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
          (operatorHeightParameter 0)).2‖ ^ 2 := by
  rw [← norm_finiteC3LegL2Extension 3
    (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
      (operatorHeightParameter 0)).2]
  congr 1
  unfold canonicalCompletedNativeC3CenterFiniteOrdinaryState
  rw [finiteC3GenuineSecondLegL2Extension_eq_prefix]
  norm_num [operatorHeightParameter]

/-- Thus the native-normalized ordinary prefix is isometric to `g₀` at the
level of its center Gram. -/
theorem norm_sq_nativeNormalizedFiniteOrdinaryState_eq_g0 :
    ‖(nativeHeightScalar 0)⁻¹ •
        canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 =
      ‖normalizedCompletedGreenState
          nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 := by
  have hGnorm : ‖nativeHeightScalar 0‖ ≠ 0 :=
    norm_ne_zero_iff.mpr nativeHeightScalar_zero_ne_zero
  rw [norm_smul, norm_inv, mul_pow,
    norm_sq_normalizedCompletedNativeC3State_zero_eq_finiteLeg,
    norm_sq_canonicalCompletedNativeC3CenterFiniteOrdinaryState]
  field_simp [hGnorm]

/-- The finite prefix carried by `g₀` is not the all-cutoff ordinary state
used by `canonicalCompletedC3CentralClockSchurEnergy`: the coordinate `3`,
which the finite port omits, is nonzero in the completed state. -/
theorem canonicalCompletedNativeC3CenterFiniteOrdinaryState_ne_completed :
    canonicalCompletedNativeC3CenterFiniteOrdinaryState ≠
      canonicalCompletedC3CentralOrdinaryState := by
  intro h
  have hcoord := congrArg (fun x : CarryVerticalL2 ↦ x 3) h
  have hstrip : (1 / 2 : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num
  have hedge := finiteReflectedGradientEdge_re_pos hstrip 3
  have hgradient : positiveDirichletGradient (1 / 2 : ℂ) 3 ≠ 0 := by
    intro hzero
    unfold finiteReflectedGradientEdge at hedge
    rw [hzero] at hedge
    simp at hedge
  apply hgradient
  simpa [canonicalCompletedNativeC3CenterFiniteOrdinaryState,
    canonicalCompletedC3CentralOrdinaryState] using hcoord.symm

/-- The existing Naimark port projection does not remove any part of `g₀`:
after the canonical finite symplectic promotion, the state is already in the
port range and is fixed pointwise. -/
theorem canonicalCompletedC3AmbientPortProjection_promoted_g0_eq_self :
    canonicalCompletedC3AmbientPortProjection
        (finiteC3SymplecticNaimarkRealization 3
          (WithLp.ofLp
            (normalizedCompletedGreenState nativeHeightScalar
              canonicalCompletedOperatorC3HilbertState 0))) =
      finiteC3SymplecticNaimarkRealization 3
        (WithLp.ofLp
          (normalizedCompletedGreenState nativeHeightScalar
            canonicalCompletedOperatorC3HilbertState 0)) := by
  unfold finiteC3SymplecticNaimarkRealization
  rw [ContinuousLinearMap.comp_apply,
    canonicalCompletedC3AmbientPortProjection_realifiedNaimarkPort]

/-! ## Canonical finite clock quotient -/

/-- The first logarithmic coordinate is nonzero. -/
theorem positiveLogDirichletGradient_half_zero_ne_zero :
    positiveLogDirichletGradient (1 / 2 : ℂ) 0 ≠ 0 := by
  rw [positiveLogDirichletGradient, positiveLogDirichletValue_zero, sub_zero]
  unfold positiveLogDirichletValue
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  · have hnorm := norm_positiveDirichletValue (1 / 2 : ℂ) 1
    apply norm_ne_zero_iff.mp
    rw [hnorm]
    positivity

/-- Hence the finite clock direction has a nonzero denominator. -/
theorem canonicalCompletedNativeC3CenterFiniteLogJetState_ne_zero :
    canonicalCompletedNativeC3CenterFiniteLogJetState ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun x : CarryVerticalL2 ↦ x 0) hzero
  apply positiveLogDirichletGradient_half_zero_ne_zero
  simpa [canonicalCompletedNativeC3CenterFiniteLogJetState] using hcoord

/-- Hilbert-forced coefficient of the clock component in the ordinary
prefix.  Lean's complex inner product is linear in the second argument. -/
def canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient : ℂ :=
  inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetState
      canonicalCompletedNativeC3CenterFiniteOrdinaryState /
    (‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ : ℂ) ^ 2

/-- Ordinary prefix after quotienting its clock direction. -/
def canonicalCompletedNativeC3CenterFiniteClockResidual : CarryVerticalL2 :=
  canonicalCompletedNativeC3CenterFiniteOrdinaryState -
    canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient •
      canonicalCompletedNativeC3CenterFiniteLogJetState

/-- The Schur coefficient is characterized by exact orthogonality. -/
theorem inner_finiteLogJet_finiteClockResidual_eq_zero :
    inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetState
      canonicalCompletedNativeC3CenterFiniteClockResidual = 0 := by
  have hnorm : ‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      canonicalCompletedNativeC3CenterFiniteLogJetState_ne_zero
  unfold canonicalCompletedNativeC3CenterFiniteClockResidual
    canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  field_simp [hnorm]
  simp

/-- The norm of the residual is the literal Schur complement. -/
theorem norm_sq_canonicalCompletedNativeC3CenterFiniteClockResidual :
    ‖canonicalCompletedNativeC3CenterFiniteClockResidual‖ ^ 2 =
      ‖canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 -
        ‖inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetState
          canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 /
          ‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ ^ 2 := by
  have hlogNorm :
      ‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      canonicalCompletedNativeC3CenterFiniteLogJetState_ne_zero
  have horth :
      inner ℂ canonicalCompletedNativeC3CenterFiniteClockResidual
        canonicalCompletedNativeC3CenterFiniteLogJetState = 0 := by
    rw [← inner_conj_symm]
    simp [inner_finiteLogJet_finiteClockResidual_eq_zero]
  have hdecomp :
      canonicalCompletedNativeC3CenterFiniteClockResidual +
          canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient •
            canonicalCompletedNativeC3CenterFiniteLogJetState =
        canonicalCompletedNativeC3CenterFiniteOrdinaryState := by
    unfold canonicalCompletedNativeC3CenterFiniteClockResidual
    abel
  have horthScaled :
      inner ℂ canonicalCompletedNativeC3CenterFiniteClockResidual
        (canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient •
          canonicalCompletedNativeC3CenterFiniteLogJetState) = 0 := by
    rw [inner_smul_right, horth, mul_zero]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    canonicalCompletedNativeC3CenterFiniteClockResidual
    (canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient •
      canonicalCompletedNativeC3CenterFiniteLogJetState) horthScaled
  rw [hdecomp] at hpyth
  have hprojection :
      ‖canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient •
          canonicalCompletedNativeC3CenterFiniteLogJetState‖ ^ 2 =
        ‖inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetState
          canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 /
          ‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ ^ 2 := by
    unfold canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient
    rw [norm_smul, norm_div, mul_pow, div_pow]
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    field_simp [hlogNorm]
  have hpyth' :
      ‖canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 =
        ‖canonicalCompletedNativeC3CenterFiniteClockResidual‖ ^ 2 +
          ‖canonicalCompletedNativeC3CenterFiniteClockProjectionCoefficient •
            canonicalCompletedNativeC3CenterFiniteLogJetState‖ ^ 2 := by
    simpa only [pow_two] using hpyth
  rw [hprojection] at hpyth'
  linarith

/-- Native-normalized positive energy left after the finite clock quotient. -/
def canonicalCompletedNativeC3CenterFiniteClockProjectedEnergy : ℝ :=
  ‖canonicalCompletedNativeC3CenterFiniteClockResidual‖ ^ 2 /
    ‖nativeHeightScalar 0‖ ^ 2

/-- Coordinate-free Schur formula with the native scalar normalization
inherited from `g₀`. -/
theorem canonicalCompletedNativeC3CenterFiniteClockProjectedEnergy_eq_schur :
    canonicalCompletedNativeC3CenterFiniteClockProjectedEnergy =
      (‖canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 -
          ‖inner ℂ canonicalCompletedNativeC3CenterFiniteLogJetState
            canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 /
            ‖canonicalCompletedNativeC3CenterFiniteLogJetState‖ ^ 2) /
        ‖nativeHeightScalar 0‖ ^ 2 := by
  unfold canonicalCompletedNativeC3CenterFiniteClockProjectedEnergy
  rw [norm_sq_canonicalCompletedNativeC3CenterFiniteClockResidual]

/-- The projected energy is nonnegative without a moment or xi hypothesis. -/
theorem canonicalCompletedNativeC3CenterFiniteClockProjectedEnergy_nonneg :
    0 ≤ canonicalCompletedNativeC3CenterFiniteClockProjectedEnergy := by
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Orthogonal clock removal can only lower the native center energy. -/
theorem canonicalCompletedNativeC3CenterFiniteClockProjectedEnergy_le_g0 :
    canonicalCompletedNativeC3CenterFiniteClockProjectedEnergy ≤
      ‖normalizedCompletedGreenState
          nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 := by
  have hGsq : 0 < ‖nativeHeightScalar 0‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr nativeHeightScalar_zero_ne_zero)
  have hresidual :
      ‖canonicalCompletedNativeC3CenterFiniteClockResidual‖ ^ 2 ≤
        ‖canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 := by
    rw [norm_sq_canonicalCompletedNativeC3CenterFiniteClockResidual]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [← norm_sq_nativeNormalizedFiniteOrdinaryState_eq_g0,
    norm_smul, norm_inv, mul_pow]
  unfold canonicalCompletedNativeC3CenterFiniteClockProjectedEnergy
  calc
    ‖canonicalCompletedNativeC3CenterFiniteClockResidual‖ ^ 2 /
          ‖nativeHeightScalar 0‖ ^ 2 ≤
        ‖canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 /
          ‖nativeHeightScalar 0‖ ^ 2 :=
      (div_le_div_iff_of_pos_right hGsq).2 hresidual
    _ = (‖nativeHeightScalar 0‖⁻¹ *
          ‖canonicalCompletedNativeC3CenterFiniteOrdinaryState‖) ^ 2 := by
      have hGnorm : ‖nativeHeightScalar 0‖ ≠ 0 :=
        norm_ne_zero_iff.mpr nativeHeightScalar_zero_ne_zero
      field_simp [hGnorm]
    _ = ‖nativeHeightScalar 0‖⁻¹ ^ 2 *
          ‖canonicalCompletedNativeC3CenterFiniteOrdinaryState‖ ^ 2 := by
      ring

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedC3CoisometricWronskianEnergyGate
import CarrySelfAdjointOperator.CompletedC3CoisometricAmbientMomentGate
import CarrySelfAdjointOperator.CompletedNativeCentralChiralEnergyFlow
import CarrySelfAdjointOperator.CompletedNativeSignedGeneratorHerglotzGram
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# First-order flatness of the central coisometric defect

The diagonal coisometric sewing balance is restricted to `z = I y` without
assuming that it vanishes on a neighborhood.  Its ambient coefficient is
extended harmlessly outside the local half-plane and proved continuous at the
center by a Tannery argument in the full completed `ℓ²` carrier.

This makes the proposed infinitesimal gate literal:

`B'(0) = 0` if and only if the native transverse curvature is four times the
completed C3 gradient energy.  Equivalently, the normalized ambient center
realizes `h₀`, and equivalently the separation-regularized C3 correction
ledger tends to zero.  The scalar gate then supplies the already isolated
one-point Herglotz positivity statement.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open Filter Topology
open CPFormal.Analytic.Cp

noncomputable section

/-- The centered transverse spectral line. -/
def canonicalCompletedC3CentralCoisometricTiltPoint (y : ℝ) : ℂ :=
  Complex.I * (y : ℂ)

@[simp] theorem canonicalCompletedC3CentralCoisometricTiltPoint_zero :
    canonicalCompletedC3CentralCoisometricTiltPoint 0 = 0 := by
  simp [canonicalCompletedC3CentralCoisometricTiltPoint]

@[simp] theorem canonicalCompletedC3CentralCoisometricTiltPoint_im (y : ℝ) :
    (canonicalCompletedC3CentralCoisometricTiltPoint y).im = y := by
  simp [canonicalCompletedC3CentralCoisometricTiltPoint]

theorem operatorHeightParameter_centralCoisometricTiltPoint_re (y : ℝ) :
    (operatorHeightParameter
      (canonicalCompletedC3CentralCoisometricTiltPoint y)).re =
      (1 / 2 : ℝ) - y := by
  norm_num [canonicalCompletedC3CentralCoisometricTiltPoint,
    operatorHeightParameter]
  ring

/-- The completed ordinary-gradient state on the central tilt line, extended
by zero outside the local half-plane.  Only its germ at zero is used. -/
def canonicalCompletedC3CentralCoisometricGradientState (y : ℝ) :
    CarryVerticalL2 :=
  if hy : y < (1 / 2 : ℝ) then
    canonicalCompletedC3DirichletGradientState
      (operatorHeightParameter
        (canonicalCompletedC3CentralCoisometricTiltPoint y))
      (by
        rw [operatorHeightParameter_centralCoisometricTiltPoint_re]
        linarith)
  else
    0

@[simp] theorem canonicalCompletedC3CentralCoisometricGradientState_zero :
    canonicalCompletedC3CentralCoisometricGradientState 0 =
      canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter 0)
        (by norm_num [operatorHeightParameter]) := by
  simp [canonicalCompletedC3CentralCoisometricGradientState,
    canonicalCompletedC3CentralCoisometricTiltPoint]

/-- Strong continuity of the full completed gradient state along an arbitrary
real central tilt, rather than only along the discrete radial sample grid. -/
theorem canonicalCompletedC3CentralCoisometricGradientState_tendsto :
    Tendsto canonicalCompletedC3CentralCoisometricGradientState
      (nhds 0)
      (nhds (canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter 0)
        (by norm_num [operatorHeightParameter]))) := by
  let parameter : ℝ → ℂ := fun y ↦
    operatorHeightParameter
      (canonicalCompletedC3CentralCoisometricTiltPoint y)
  have hparameter : Tendsto parameter (nhds 0)
      (nhds (operatorHeightParameter 0)) := by
    have hcontinuous : ContinuousAt parameter 0 := by
      dsimp only [parameter]
      unfold canonicalCompletedC3CentralCoisometricTiltPoint
        operatorHeightParameter
      fun_prop
    simpa [parameter, canonicalCompletedC3CentralCoisometricTiltPoint] using
      hcontinuous.tendsto
  have hre : Tendsto (fun y ↦ (parameter y).re) (nhds 0)
      (nhds (1 / 2 : ℝ)) := by
    simpa [Function.comp_def, operatorHeightParameter] using
      Complex.continuous_re.continuousAt.tendsto.comp hparameter
  have hnorm : Tendsto (fun y ↦ ‖parameter y‖) (nhds 0)
      (nhds (1 / 2 : ℝ)) := by
    simpa [Function.comp_def, operatorHeightParameter] using
      tendsto_norm.comp hparameter
  have hreEventually : ∀ᶠ y : ℝ in nhds 0,
      (1 / 4 : ℝ) < (parameter y).re :=
    (tendsto_order.1 hre).1 _ (by norm_num)
  have hnormEventually : ∀ᶠ y : ℝ in nhds 0,
      ‖parameter y‖ < (1 : ℝ) :=
    (tendsto_order.1 hnorm).2 _ (by norm_num)
  let bound : ℕ → ℝ := fun n ↦
    (((n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))
  have hboundSummable : Summable bound := by
    have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 4 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have hshift := hbase.comp_injective
      (show Function.Injective (fun n : ℕ ↦ n + 1) by
        intro a b hab
        exact Nat.add_right_cancel hab)
    simpa [bound, Function.comp_def] using hshift
  have hterm (n : ℕ) :
      Tendsto
        (fun y : ℝ ↦
          (lp.single 2 n (positiveDirichletGradient (parameter y) n) :
            CarryVerticalL2))
        (nhds 0)
        (nhds (lp.single 2 n
          (positiveDirichletGradient (operatorHeightParameter 0) n) :
            CarryVerticalL2)) := by
    have hcoordinate :=
      (positiveDirichletGradient_continuous n).continuousAt.tendsto.comp
        hparameter
    simpa only [lp.singleContinuousLinearMap_apply, Function.comp_def] using
      (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 2 n).continuous
        |>.continuousAt.tendsto.comp hcoordinate
  have htermBound : ∀ᶠ y : ℝ in nhds 0, ∀ n : ℕ,
      ‖(lp.single 2 n (positiveDirichletGradient (parameter y) n) :
        CarryVerticalL2)‖ ≤ bound n := by
    filter_upwards [hreEventually, hnormEventually] with y hyRe hyNorm
    intro n
    have hyPos : 0 < (parameter y).re := by linarith
    have hgradient := norm_positiveDirichletGradient_le hyPos n
    have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : n + 1 ≠ 0)
    have hexponent : -(parameter y).re - 1 ≤ (-5 / 4 : ℝ) := by
      linarith
    rw [lp.norm_single (by norm_num)]
    calc
      ‖positiveDirichletGradient (parameter y) n‖ ≤
          ‖parameter y‖ *
            ((n + 1 : ℕ) : ℝ) ^ (-(parameter y).re - 1) := hgradient
      _ ≤ 1 * ((n + 1 : ℕ) : ℝ) ^ (-(parameter y).re - 1) := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hyNorm)
          (Real.rpow_nonneg (zero_le_one.trans hbase) _)
      _ ≤ 1 * ((n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hbase hexponent) zero_le_one
      _ = bound n := by simp [bound]
  have htannery := tendsto_tsum_of_dominated_convergence
    hboundSummable hterm htermBound
  have hsource (y : ℝ) (hy : y < (1 / 2 : ℝ)) :
      (∑' n : ℕ,
        (lp.single 2 n (positiveDirichletGradient (parameter y) n) :
          CarryVerticalL2)) =
        canonicalCompletedC3CentralCoisometricGradientState y := by
    rw [canonicalCompletedC3CentralCoisometricGradientState, dif_pos hy]
    exact (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num)
      (canonicalCompletedC3DirichletGradientState
        (parameter y) (by
          dsimp only [parameter]
          rw [operatorHeightParameter_centralCoisometricTiltPoint_re]
          linarith))).tsum_eq
  have htarget :
      (∑' n : ℕ,
        (lp.single 2 n
          (positiveDirichletGradient (operatorHeightParameter 0) n) :
            CarryVerticalL2)) =
        canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0)
          (by norm_num [operatorHeightParameter]) := by
    exact (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num)
      (canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter 0)
        (by norm_num [operatorHeightParameter]))).tsum_eq
  rw [htarget] at htannery
  apply htannery.congr'
  filter_upwards [hreEventually] with y hyRe
  have hy : y < (1 / 2 : ℝ) := by
    have hparameterRe : (parameter y).re = (1 / 2 : ℝ) - y := by
      dsimp only [parameter]
      exact operatorHeightParameter_centralCoisometricTiltPoint_re y
    rw [hparameterRe] at hyRe
    linarith
  exact hsource y hy

/-- The scalar ambient coefficient in the diagonal balance.  On the local
half-plane this is exactly the full ambient response energy after eliminating
the Naimark view in favor of the ordinary completed gradient. -/
def canonicalCompletedC3CentralCoisometricAmbientEnergy (y : ℝ) : ℝ :=
  (completedC3RadialRealCoefficient
      (operatorHeightParameter
        (canonicalCompletedC3CentralCoisometricTiltPoint y)) ^ 2 + 1) *
    ‖canonicalCompletedC3CentralCoisometricGradientState y‖ ^ 2

@[simp] theorem canonicalCompletedC3CentralCoisometricAmbientEnergy_zero :
    canonicalCompletedC3CentralCoisometricAmbientEnergy 0 =
      2 * ‖canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter 0)
        (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  unfold canonicalCompletedC3CentralCoisometricAmbientEnergy
  rw [canonicalCompletedC3CentralCoisometricTiltPoint_zero,
    canonicalCompletedC3CentralCoisometricGradientState_zero,
    completedC3RadialRealCoefficient_operatorHeightParameter_zero]
  ring

/-- The ambient coefficient needs only continuity, not differentiability, for
the derivative of `y A(y)` at the center. -/
theorem canonicalCompletedC3CentralCoisometricAmbientEnergy_continuousAt :
    ContinuousAt canonicalCompletedC3CentralCoisometricAmbientEnergy 0 := by
  have hgradient :
      ContinuousAt canonicalCompletedC3CentralCoisometricGradientState 0 := by
    change Tendsto canonicalCompletedC3CentralCoisometricGradientState
      (nhds 0)
      (nhds (canonicalCompletedC3CentralCoisometricGradientState 0))
    rw [canonicalCompletedC3CentralCoisometricGradientState_zero]
    exact canonicalCompletedC3CentralCoisometricGradientState_tendsto
  have hradial : ContinuousAt
      (fun y : ℝ ↦ completedC3RadialRealCoefficient
        (operatorHeightParameter
          (canonicalCompletedC3CentralCoisometricTiltPoint y))) 0 := by
    have hexponent : Tendsto
        (fun y : ℝ ↦
          -criticalDisplacement
            (operatorHeightParameter
              (canonicalCompletedC3CentralCoisometricTiltPoint y)).re)
        (nhds 0) (nhds 0) := by
      have hcontinuous : ContinuousAt
          (fun y : ℝ ↦
            -criticalDisplacement
              (operatorHeightParameter
                (canonicalCompletedC3CentralCoisometricTiltPoint y)).re) 0 := by
        unfold criticalDisplacement operatorHeightParameter
          canonicalCompletedC3CentralCoisometricTiltPoint
        fun_prop
      simpa [criticalDisplacement, operatorHeightParameter,
        canonicalCompletedC3CentralCoisometricTiltPoint] using
          hcontinuous.tendsto
    have hpow :=
      (Real.continuousAt_const_rpow (by norm_num : (3 : ℝ) ≠ 0)).tendsto.comp
        hexponent
    simpa [ContinuousAt, completedC3RadialRealCoefficient,
      Function.comp_def] using hpow
  exact ((hradial.pow 2).add continuousAt_const).mul
    (hgradient.norm.pow 2)

/-- A continuous coefficient multiplied by the centered coordinate has the
expected derivative at zero. -/
private theorem hasDerivAt_id_mul_of_continuousAt
    (f : ℝ → ℝ) (hf : ContinuousAt f 0) :
    HasDerivAt (fun y ↦ y * f y) (f 0) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hsmall :=
    (Asymptotics.isBigO_refl (fun h : ℝ ↦ h) (nhds 0)).mul_isLittleO
      hf.isLittleO
  exact hsmall.congr'
    (Eventually.of_forall fun h ↦ by simp; ring)
    (Eventually.of_forall fun h ↦ by simp)

/-- The actual central defect `B(y) = 2 y A(y) - E'(y)`. -/
def canonicalCompletedC3CentralCoisometricEnergyDefect (y : ℝ) : ℝ :=
  2 * y * canonicalCompletedC3CentralCoisometricAmbientEnergy y -
    deriv (completedNativeVerticalModulusEnergy 0) y

/-- The derivative of the central defect is exactly the difference between
the geometric `4 = 2 × 2` energy and the native transverse curvature. -/
theorem hasDerivAt_canonicalCompletedC3CentralCoisometricEnergyDefect_zero :
    HasDerivAt canonicalCompletedC3CentralCoisometricEnergyDefect
      (4 * ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0)
          (by norm_num [operatorHeightParameter])‖ ^ 2 -
        iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0) 0 := by
  have hambient :=
    (hasDerivAt_id_mul_of_continuousAt
      canonicalCompletedC3CentralCoisometricAmbientEnergy
      canonicalCompletedC3CentralCoisometricAmbientEnergy_continuousAt).const_mul 2
  have hnative :=
    hasDerivAt_deriv_completedNativeVerticalModulusEnergy_zero
  have hderiv := hambient.sub hnative
  have hfun :
      canonicalCompletedC3CentralCoisometricEnergyDefect =
        (fun y ↦ 2 *
          (y * canonicalCompletedC3CentralCoisometricAmbientEnergy y)) -
          deriv (completedNativeVerticalModulusEnergy 0) := by
    funext y
    simp [canonicalCompletedC3CentralCoisometricEnergyDefect]
    ring
  rw [hfun]
  have hcoefficient :
      2 * canonicalCompletedC3CentralCoisometricAmbientEnergy 0 -
          iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 =
        4 * ‖canonicalCompletedC3DirichletGradientState
            (operatorHeightParameter 0)
            (by norm_num [operatorHeightParameter])‖ ^ 2 -
          iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 := by
    rw [canonicalCompletedC3CentralCoisometricAmbientEnergy_zero]
    ring
  exact hderiv.congr_deriv hcoefficient

theorem deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero :
    deriv canonicalCompletedC3CentralCoisometricEnergyDefect 0 =
      4 * ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0)
          (by norm_num [operatorHeightParameter])‖ ^ 2 -
        iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 :=
  hasDerivAt_canonicalCompletedC3CentralCoisometricEnergyDefect_zero.deriv

/-- First-order flatness of the central defect is exactly the previously
isolated transverse-curvature gate. -/
theorem
    deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero_eq_zero_iff :
    deriv canonicalCompletedC3CentralCoisometricEnergyDefect 0 = 0 ↔
      iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 =
        4 * ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0)
          (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  rw [deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero]
  constructor <;> intro h <;> linarith

/-- The same flatness gate in normalized ambient-moment coordinates. -/
theorem
    deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero_eq_zero_iff_moment :
    deriv canonicalCompletedC3CentralCoisometricEnergyDefect 0 = 0 ↔
      ‖canonicalCompletedC3NormalizedAmbientResponseState 0
          (by norm_num [operatorHeightParameter])‖ ^ 2 =
        canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero_eq_zero_iff]
  exact
    norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero_eq_moment_zero_iff_transverseCurvature.symm

/-- The continuous defect agrees locally with the exact TFVD/coisometric
Wronskian balance.  Thus its derivative is attached to the existing sewing
object rather than to a newly fitted scalar model. -/
theorem canonicalCompletedC3CentralCoisometricEnergyDefect_eq_balance
    { ι : Type* } [Fintype ι]
    (M : ℕ) (y : ℝ)
    (hyStrip : operatorHeightParameter
      (canonicalCompletedC3CentralCoisometricTiltPoint y) ∈
        genuineCriticalStrip)
    (legs : ReflectedBoundarySynthesisData ι) :
    canonicalCompletedC3CentralCoisometricEnergyDefect y =
      canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
        M (canonicalCompletedC3CentralCoisometricTiltPoint y) hyStrip.1 := by
  rw [canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_eq_gradient_sub_verticalModulusEnergy_deriv
    M (canonicalCompletedC3CentralCoisometricTiltPoint y) hyStrip legs]
  have hy : y < (1 / 2 : ℝ) := by
    have hpos := hyStrip.1
    rw [operatorHeightParameter_centralCoisometricTiltPoint_re] at hpos
    linarith
  have hshift :
      deriv
          (completedNativeVerticalModulusEnergy
            (canonicalCompletedC3CentralCoisometricTiltPoint y)) 0 =
        deriv (completedNativeVerticalModulusEnergy 0) y := by
    have hfun :
        completedNativeVerticalModulusEnergy
            (canonicalCompletedC3CentralCoisometricTiltPoint y) =
          fun t : ℝ ↦ completedNativeVerticalModulusEnergy 0 (y + t) := by
      funext t
      unfold completedNativeVerticalModulusEnergy
        canonicalCompletedC3CentralCoisometricTiltPoint
      congr 2
      push_cast
      ring
    rw [hfun, deriv_comp_const_add]
    simp
  rw [hshift]
  unfold canonicalCompletedC3CentralCoisometricEnergyDefect
    canonicalCompletedC3CentralCoisometricAmbientEnergy
    canonicalCompletedC3CentralCoisometricGradientState
  rw [dif_pos hy]
  simp [canonicalCompletedC3CentralCoisometricTiltPoint]

/-- Four-channel discrete spelling: the first-order defect is flat exactly
when the separation-regularized ambient correction ledger vanishes in the
central radial limit. -/
theorem
    deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero_eq_zero_iff_regularizedLedger
    (M N : ℕ) (i j : Fin N) :
    deriv canonicalCompletedC3CentralCoisometricEnergyDefect 0 = 0 ↔
      Tendsto
        (fun k : ℕ ↦
          canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger
            k N i j)
        atTop (nhds 0) := by
  rw [deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero_eq_zero_iff_moment]
  rw [canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger_tendsto_zero_iff
    M N i j]
  rw [inner_self_eq_norm_sq_to_K]
  constructor
  · intro hreal
    calc
      ((↑‖canonicalCompletedC3NormalizedAmbientResponseState 0
          (by norm_num [operatorHeightParameter])‖ : ℂ) ^ 2) =
          ((‖canonicalCompletedC3NormalizedAmbientResponseState 0
            (by norm_num [operatorHeightParameter])‖ ^ 2 : ℝ) : ℂ) :=
        (Complex.ofReal_pow _ _).symm
      _ = (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) :=
        congrArg Complex.ofReal hreal
  · intro hcomplex
    have hre := congrArg Complex.re hcomplex
    norm_num [pow_two, Complex.mul_re] at hre
    simpa [pow_two] using hre

/-- The flatness gate closes the one-point Herglotz section.  Higher sections
still require genuinely polarized information. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_one_eventually_posSemidef_of_centralCoisometricDefectFlat
    (hflat : deriv canonicalCompletedC3CentralCoisometricEnergyDefect 0 = 0) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 1).PosSemidef := by
  exact
    canonicalCompletedNativeRadialHerglotzSampleMatrix_one_eventually_posSemidef_of_transverseCurvature
      (deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero_eq_zero_iff.mp
        hflat)

end

end CarrySelfAdjointOperator

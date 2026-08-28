import CarrySelfAdjointOperator.CompletedC3ArchimedeanChartOperatorCarrier
import CarrySelfAdjointOperator.CompletedC3SymplecticNaimarkVectorLimit
import CarrySelfAdjointOperator.CompletedNativeTfvdCoefficientJets
import Mathlib.Tactic

/-!
# Operator carrier for the completed global Green kernel

The mixed radial coefficient is a difference of two canonical camera weights.
This module keeps that difference division-free by placing the weighted radial
state and the ordinary radial state in a two-channel Hilbert carrier.  The
canonical symplectic rotation then reads the coefficient times the positive
radial Gram without choosing a square root or hiding a sign.

The resulting radial block is combined with the independently constructed
archimedean/chart block only in the final direct-sum operator carrier.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The real camera weight whose direct/reflected difference is the mixed
radial coefficient. -/
def canonicalC3RadialBoundaryWeight (z : ℂ) : ℂ :=
  (((3 : ℝ) ^ (-criticalDisplacement z.re) : ℝ) : ℂ)

theorem canonicalC3MixedRadialCoefficient_eq_weight_sub
    (z w : ℂ) :
    canonicalC3MixedRadialCoefficient z w =
      canonicalC3RadialBoundaryWeight (reflectedParameter z) -
        canonicalC3RadialBoundaryWeight w :=
  rfl

@[simp] theorem starRingEnd_canonicalC3RadialBoundaryWeight
    (z : ℂ) :
    (starRingEnd ℂ) (canonicalC3RadialBoundaryWeight z) =
      canonicalC3RadialBoundaryWeight z := by
  simp [canonicalC3RadialBoundaryWeight]

/-- Two-channel Hilbert carrier of the weighted and ordinary radial states. -/
abbrev CanonicalCompletedC3RadialOperatorCarrier :=
  WithLp 2 (CarryVerticalL2 × CarryVerticalL2)

/-- Radial boundary state `(a(z) g(z), g(z))`. -/
def canonicalCompletedC3RadialOperatorState
    (z : ℂ) (hz : 0 < z.re) : CanonicalCompletedC3RadialOperatorCarrier :=
  let radial := completedC3RadialAllOrderState z hz
  WithLp.toLp 2 (canonicalC3RadialBoundaryWeight z • radial, radial)

/-- Bounded symplectic rotation on the radial boundary carrier. -/
def canonicalCompletedC3RadialSymplecticRotation :
    CanonicalCompletedC3RadialOperatorCarrier →L[ℂ]
      CanonicalCompletedC3RadialOperatorCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ CarryVerticalL2 CarryVerticalL2).symm
    |>.toContinuousLinearMap.comp
      ((-(WithLp.sndL 2 ℂ CarryVerticalL2 CarryVerticalL2)).prod
        (WithLp.fstL 2 ℂ CarryVerticalL2 CarryVerticalL2))

@[simp] theorem canonicalCompletedC3RadialSymplecticRotation_apply
    (state : CanonicalCompletedC3RadialOperatorCarrier) :
    canonicalCompletedC3RadialSymplecticRotation state =
      WithLp.toLp 2 (-state.snd, state.fst) :=
  rfl

@[simp] theorem canonicalCompletedC3RadialSymplecticRotation_sq
    (state : CanonicalCompletedC3RadialOperatorCarrier) :
    canonicalCompletedC3RadialSymplecticRotation
        (canonicalCompletedC3RadialSymplecticRotation state) = -state := by
  apply WithLp.ofLp_injective 2
  ext <;> rfl

/-- The completed mixed radial Green kernel is exactly a bounded-operator
readout on the radial Hilbert carrier. -/
theorem canonicalCompletedC3MixedRadialGreenKernel_eq_operatorInner
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    canonicalCompletedC3MixedRadialGreenKernel z w hw hzReflected =
      inner ℂ
        (canonicalCompletedC3RadialOperatorState w hw)
        (canonicalCompletedC3RadialSymplecticRotation
          (canonicalCompletedC3RadialOperatorState
            (reflectedParameter z) hzReflected)) := by
  unfold canonicalCompletedC3MixedRadialGreenKernel
  rw [canonicalC3MixedRadialCoefficient_eq_weight_sub]
  rw [← completedC3RadialAllOrderGram_eq_rawGammaGram]
  unfold completedC3RadialAllOrderGram
    canonicalCompletedC3RadialOperatorState
  simp [canonicalCompletedC3RadialSymplecticRotation,
    WithLp.prod_inner_apply, inner_smul_left, inner_smul_right]
  ring

/-! ## Direct-sum realization of the global kernel -/

/-- Hilbert carrier containing the radial boundary block and the crossed
archimedean/chart block. -/
abbrev CanonicalCompletedC3GlobalGreenOperatorCarrier :=
  WithLp 2
    (CanonicalCompletedC3RadialOperatorCarrier ×
      CanonicalCompletedC3ArchimedeanChartOperatorCarrier)

/-- Direct state at the response parameter. -/
def canonicalCompletedC3GlobalGreenResponseState
    (w : ℂ) (hw : 0 < (operatorHeightParameter w).re) :
    CanonicalCompletedC3GlobalGreenOperatorCarrier :=
  WithLp.toLp 2
    (nativeXiCompletionFactor w •
        canonicalCompletedC3RadialOperatorState
          (operatorHeightParameter w) hw,
      canonicalCompletedC3ArchimedeanChartOperatorState w)

/-- Reflected state at the source parameter.  Only the radial geometric
coordinate is reflected; the crossed archimedean/chart trace keeps the
original height parameter used by its product rule. -/
def canonicalCompletedC3GlobalGreenReflectedState
    (z : ℂ)
    (hzReflected :
      0 < (reflectedParameter (operatorHeightParameter z)).re) :
    CanonicalCompletedC3GlobalGreenOperatorCarrier :=
  WithLp.toLp 2
    (nativeXiCompletionFactor z •
        canonicalCompletedC3RadialOperatorState
          (reflectedParameter (operatorHeightParameter z)) hzReflected,
      canonicalCompletedC3ArchimedeanChartOperatorState z)

/-- Bounded block operator reading both retained global Green channels. -/
def canonicalCompletedC3GlobalGreenOperator :
    CanonicalCompletedC3GlobalGreenOperatorCarrier →L[ℂ]
      CanonicalCompletedC3GlobalGreenOperatorCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      CanonicalCompletedC3RadialOperatorCarrier
      CanonicalCompletedC3ArchimedeanChartOperatorCarrier).symm
    |>.toContinuousLinearMap.comp
      ((canonicalCompletedC3RadialSymplecticRotation.comp
          (WithLp.fstL 2 ℂ
            CanonicalCompletedC3RadialOperatorCarrier
            CanonicalCompletedC3ArchimedeanChartOperatorCarrier)).prod
        (canonicalCompletedC3ArchimedeanChartOperator.comp
          (WithLp.sndL 2 ℂ
            CanonicalCompletedC3RadialOperatorCarrier
            CanonicalCompletedC3ArchimedeanChartOperatorCarrier)))

@[simp] theorem canonicalCompletedC3GlobalGreenOperator_apply
    (state : CanonicalCompletedC3GlobalGreenOperatorCarrier) :
    canonicalCompletedC3GlobalGreenOperator state = WithLp.toLp 2
      (canonicalCompletedC3RadialSymplecticRotation state.fst,
        canonicalCompletedC3ArchimedeanChartOperator state.snd) :=
  rfl

@[simp] theorem canonicalCompletedC3GlobalGreenOperator_sq
    (state : CanonicalCompletedC3GlobalGreenOperatorCarrier) :
    canonicalCompletedC3GlobalGreenOperator
        (canonicalCompletedC3GlobalGreenOperator state) = -state := by
  rw [canonicalCompletedC3GlobalGreenOperator_apply,
    canonicalCompletedC3GlobalGreenOperator_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact canonicalCompletedC3RadialSymplecticRotation_sq state.fst
  · exact canonicalCompletedC3ArchimedeanChartOperator_sq state.snd

@[simp] theorem canonicalCompletedC3GlobalGreenResponseState_fst
    (w : ℂ) (hw : 0 < (operatorHeightParameter w).re) :
    (canonicalCompletedC3GlobalGreenResponseState w hw).fst =
      nativeXiCompletionFactor w •
        canonicalCompletedC3RadialOperatorState
          (operatorHeightParameter w) hw :=
  rfl

@[simp] theorem canonicalCompletedC3GlobalGreenResponseState_snd
    (w : ℂ) (hw : 0 < (operatorHeightParameter w).re) :
    (canonicalCompletedC3GlobalGreenResponseState w hw).snd =
      canonicalCompletedC3ArchimedeanChartOperatorState w :=
  rfl

@[simp] theorem canonicalCompletedC3GlobalGreenReflectedState_fst
    (z : ℂ)
    (hzReflected :
      0 < (reflectedParameter (operatorHeightParameter z)).re) :
    (canonicalCompletedC3GlobalGreenReflectedState z hzReflected).fst =
      nativeXiCompletionFactor z •
        canonicalCompletedC3RadialOperatorState
          (reflectedParameter (operatorHeightParameter z)) hzReflected :=
  rfl

@[simp] theorem canonicalCompletedC3GlobalGreenReflectedState_snd
    (z : ℂ)
    (hzReflected :
      0 < (reflectedParameter (operatorHeightParameter z)).re) :
    (canonicalCompletedC3GlobalGreenReflectedState z hzReflected).snd =
      canonicalCompletedC3ArchimedeanChartOperatorState z :=
  rfl

/-- Expands only the outer direct sum, retaining both channel readouts. -/
theorem canonicalCompletedC3GlobalGreenOperator_inner
    (x y : CanonicalCompletedC3GlobalGreenOperatorCarrier) :
    inner ℂ x (canonicalCompletedC3GlobalGreenOperator y) =
      inner ℂ x.fst
          (canonicalCompletedC3RadialSymplecticRotation y.fst) +
        inner ℂ x.snd
          (canonicalCompletedC3ArchimedeanChartOperator y.snd) := by
  rw [canonicalCompletedC3GlobalGreenOperator_apply,
    WithLp.prod_inner_apply]
  rfl

/-- Exact bounded-operator realization of the completed candidate global
Green kernel.  The radial and archimedean/chart channels remain separate up
to the outer Hilbert direct sum. -/
theorem canonicalCompletedC3FNegFPrimeMixedGreenKernel_eq_operatorInner
    {z w : ℂ} (hw : 0 < (operatorHeightParameter w).re)
    (hzReflected :
      0 < (reflectedParameter (operatorHeightParameter z)).re) :
    canonicalCompletedC3FNegFPrimeMixedGreenKernel
        z w hw hzReflected =
      inner ℂ
        (canonicalCompletedC3GlobalGreenResponseState w hw)
        (canonicalCompletedC3GlobalGreenOperator
          (canonicalCompletedC3GlobalGreenReflectedState z hzReflected)) := by
  unfold canonicalCompletedC3FNegFPrimeMixedGreenKernel
  rw [canonicalCompletedC3GlobalGreenOperator_inner]
  simp only [canonicalCompletedC3GlobalGreenResponseState_fst,
    canonicalCompletedC3GlobalGreenResponseState_snd,
    canonicalCompletedC3GlobalGreenReflectedState_fst,
    canonicalCompletedC3GlobalGreenReflectedState_snd,
    map_smul, inner_smul_left, inner_smul_right]
  rw [← canonicalCompletedC3MixedRadialGreenKernel_eq_operatorInner,
    ← canonicalCompletedC3ArchimedeanChartMixedChannel_eq_operatorInner]
  unfold mixedHermitianWeight
  ring

/-! ## Forward-difference jets of an operator-valued kernel -/

/-- Mixed forward differences commute with a fixed bounded operator between
the two state channels. -/
theorem completedGreenOperatorKernel_mixedForwardDifference_eq_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (response source : ℂ → E)
    (h : ℂ) (p q : ℕ) :
    (completedGreenForwardDifference h)^[p]
        (fun w ↦ (completedGreenForwardDifference h)^[q]
          (fun z ↦ inner ℂ (response w) (T (source z))) 0) 0 =
      inner ℂ
        ((completedGreenForwardDifference h)^[p] response 0)
        (T ((completedGreenForwardDifference h)^[q] source 0)) := by
  have hright :
      (fun w ↦ (completedGreenForwardDifference h)^[q]
        (fun z ↦ inner ℂ (response w) (T (source z))) 0) =
      (fun w ↦ inner ℂ (response w)
        (T ((completedGreenForwardDifference h)^[q] source 0))) := by
    funext w
    rw [congrFun
      (completedGreenForwardDifference_iter_inner_right h
        (fun z ↦ T (source z)) (response w) q) 0]
    congr 1
    exact congrFun
      (completedGreenForwardDifference_iter_linearMap
        T.toLinearMap h source q) 0
  rw [hright]
  exact congrFun
    (completedGreenForwardDifference_iter_inner_left h response
      (T ((completedGreenForwardDifference h)^[q] source 0)) p) 0

/-- Normalized operator jets are exactly the normalized mixed forward
difference of their scalar operator kernel. -/
theorem inner_completedGreenForwardDifferenceJet_operator_eq_kernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (response source : ℂ → E)
    (h : ℂ) (p q : ℕ) :
    inner ℂ
        (completedGreenForwardDifferenceJet response h p)
        (T (completedGreenForwardDifferenceJet source h q)) =
      completedGreenKernelForwardDifference
        (fun w z ↦ inner ℂ (response w) (T (source z))) h p q := by
  unfold completedGreenForwardDifferenceJet
    completedGreenKernelForwardDifference
  rw [map_smul, inner_smul_left, inner_smul_right,
    completedGreenOperatorKernel_mixedForwardDifference_eq_inner]
  ring

theorem operatorHeightParameter_ofReal_re_pos (z : ℂ) :
    0 < (operatorHeightParameter (z.re : ℂ)).re := by
  norm_num [operatorHeightParameter]

theorem reflected_operatorHeightParameter_ofReal_re_pos (z : ℂ) :
    0 < (reflectedParameter
      (operatorHeightParameter (z.re : ℂ))).re := by
  norm_num [operatorHeightParameter, reflectedParameter]

/-- Global response state restricted to the centered real-height axis. -/
def canonicalCompletedC3GlobalGreenResponseRealAxisState
    (z : ℂ) : CanonicalCompletedC3GlobalGreenOperatorCarrier :=
  canonicalCompletedC3GlobalGreenResponseState (z.re : ℂ)
    (operatorHeightParameter_ofReal_re_pos z)

/-- Global reflected source state restricted to the same real-height axis. -/
def canonicalCompletedC3GlobalGreenReflectedRealAxisState
    (z : ℂ) : CanonicalCompletedC3GlobalGreenOperatorCarrier :=
  canonicalCompletedC3GlobalGreenReflectedState (z.re : ℂ)
    (reflected_operatorHeightParameter_ofReal_re_pos z)

/-- Pointwise real-axis realization of the candidate global kernel. -/
theorem canonicalCompletedC3FNegFPrimeMixedGreenKernel_realAxis_eq_operatorInner
    (z w : ℂ) :
    canonicalCompletedC3FNegFPrimeMixedGreenKernel
        (z.re : ℂ) (w.re : ℂ)
        (operatorHeightParameter_ofReal_re_pos w)
        (reflected_operatorHeightParameter_ofReal_re_pos z) =
      inner ℂ
        (canonicalCompletedC3GlobalGreenResponseRealAxisState w)
        (canonicalCompletedC3GlobalGreenOperator
          (canonicalCompletedC3GlobalGreenReflectedRealAxisState z)) := by
  exact canonicalCompletedC3FNegFPrimeMixedGreenKernel_eq_operatorInner
    (operatorHeightParameter_ofReal_re_pos w)
    (reflected_operatorHeightParameter_ofReal_re_pos z)

/-- Every finite pair of real-axis geometric jets realizes exactly the
corresponding normalized forward difference of the candidate global kernel.
This is the jet-level consequence of the Hilbertization; no moment or
positivity identification is assumed. -/
theorem canonicalCompletedC3GlobalGreenOperatorJets_eq_kernelForwardDifference
    (h : ℂ) (p q : ℕ) :
    inner ℂ
        (completedGreenForwardDifferenceJet
          canonicalCompletedC3GlobalGreenResponseRealAxisState h p)
        (canonicalCompletedC3GlobalGreenOperator
          (completedGreenForwardDifferenceJet
            canonicalCompletedC3GlobalGreenReflectedRealAxisState h q)) =
      completedGreenKernelForwardDifference
        (fun w z ↦ canonicalCompletedC3FNegFPrimeMixedGreenKernel
          (z.re : ℂ) (w.re : ℂ)
          (operatorHeightParameter_ofReal_re_pos w)
          (reflected_operatorHeightParameter_ofReal_re_pos z)) h p q := by
  rw [inner_completedGreenForwardDifferenceJet_operator_eq_kernel]
  congr 1
  funext w z
  exact
    (canonicalCompletedC3FNegFPrimeMixedGreenKernel_realAxis_eq_operatorInner
      z w).symm

end

end CarrySelfAdjointOperator

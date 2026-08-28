import CarrySelfAdjointOperator.CompletedNativeTfvdCoefficientJets
import CarrySelfAdjointOperator.CompletedC3ConcreteRealAxisKernelCarrier
import CarrySelfAdjointOperator.CompletedNativePositiveJacobiResolventAnalytic
import Mathlib.Tactic

/-!
# Direct HP carrier from the completed TFVD coefficient jets

The completed positive carrier keeps ordinary, logarithmic, and boundary
information separated.  This module reads one exact slope coordinate from the
ordinary or logarithmic channel and identifies the completed parity jets with
the logarithmic-orbit coefficient family proved independent in
`CompletedNativeTfvdCoefficientJets`.

No fixed camera, Gram argument for independence, zero condition, or spectral
hypothesis is used.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-! ## Exact coordinate readouts of the separated positive carrier -/

/-- Parseval probe representing evaluation at one ordinary TFVD slope
coordinate. -/
def canonicalCompletedC3SlopeParsevalProbe
    (n : ℕ) : CanonicalCompletedGreenFrameCarrier :=
  canonicalCompletedGreenFrameParsevalAnalysis (lp.single 2 n (1 : ℂ))

/-- Continuous readout of one ordinary slope coordinate. -/
def canonicalCompletedC3OrdinarySlopeCoordinateReadout
    (n : ℕ) : CanonicalCompletedC3RealAxisPositiveCarrier →L[ℂ] ℂ :=
  (innerSL ℂ (canonicalCompletedC3SlopeParsevalProbe n)).comp
    (WithLp.fstL 2 ℂ
      CanonicalCompletedGreenFrameCarrier
      (WithLp 2
        (CanonicalCompletedGreenFrameCarrier ×
          RealHilbertComplexification
            CanonicalCompletedC3RealAxisResidualHilbert)))

/-- Continuous readout of one logarithmic slope coordinate. -/
def canonicalCompletedC3LogJetSlopeCoordinateReadout
    (n : ℕ) : CanonicalCompletedC3RealAxisPositiveCarrier →L[ℂ] ℂ :=
  (innerSL ℂ (canonicalCompletedC3SlopeParsevalProbe n)).comp
    ((WithLp.fstL 2 ℂ
      CanonicalCompletedGreenFrameCarrier
      (RealHilbertComplexification
        CanonicalCompletedC3RealAxisResidualHilbert)).comp
      (WithLp.sndL 2 ℂ
        CanonicalCompletedGreenFrameCarrier
        (WithLp 2
          (CanonicalCompletedGreenFrameCarrier ×
            RealHilbertComplexification
              CanonicalCompletedC3RealAxisResidualHilbert))))

@[simp] theorem canonicalCompletedC3OrdinarySlopeCoordinateReadout_positiveState
    (n : ℕ) (z : ℂ) :
    canonicalCompletedC3OrdinarySlopeCoordinateReadout n
        (canonicalCompletedC3RealAxisPositiveState z) =
      positiveDirichletGradient (operatorHeightParameter (z.re : ℂ)) n := by
  rw [canonicalCompletedC3OrdinarySlopeCoordinateReadout,
    ContinuousLinearMap.comp_apply, WithLp.fstL_apply]
  change inner ℂ (canonicalCompletedC3SlopeParsevalProbe n)
      (canonicalCompletedC3RealAxisPositiveState z).ordinary = _
  rw [
    canonicalCompletedC3RealAxisPositiveState_ordinary,
    canonicalCompletedC3SlopeParsevalProbe,
    canonicalCompletedGreenFrameParsevalAnalysis_inner,
    lp.inner_single_left]
  simp [canonicalCompletedC3RealAxisOrdinaryState,
    canonicalCompletedC3HilbertState]

@[simp] theorem canonicalCompletedC3LogJetSlopeCoordinateReadout_positiveState
    (n : ℕ) (z : ℂ) :
    canonicalCompletedC3LogJetSlopeCoordinateReadout n
        (canonicalCompletedC3RealAxisPositiveState z) =
      positiveLogDirichletGradient (operatorHeightParameter (z.re : ℂ)) n := by
  rw [canonicalCompletedC3LogJetSlopeCoordinateReadout,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    WithLp.sndL_apply, WithLp.fstL_apply]
  change inner ℂ (canonicalCompletedC3SlopeParsevalProbe n)
      (canonicalCompletedC3RealAxisPositiveState z).logJet = _
  rw [
    canonicalCompletedC3RealAxisPositiveState_logJet,
    canonicalCompletedC3SlopeParsevalProbe,
    canonicalCompletedGreenFrameParsevalAnalysis_inner,
    lp.inner_single_left]
  simp [canonicalCompletedC3RealAxisLogJetState,
    canonicalCompletedC3HilbertState]

/-! ## Exact passage from normalized samples to the positive state -/

/-- Canonical forward differences sample only the real axis, so inserting a
real-part restriction into a state does not alter any finite jet. -/
theorem completedGreenForwardDifferenceJet_realAxisRestriction
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (state : ℂ → E) (k order : ℕ) :
    completedGreenForwardDifferenceJet
        (fun z ↦ state (z.re : ℂ)) (canonicalGreenJetStep k) order =
      completedGreenForwardDifferenceJet state
        (canonicalGreenJetStep k) order := by
  unfold completedGreenForwardDifferenceJet
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift,
    completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply congrArg state
  have hpoint := nsmul_canonicalGreenJetStep_eq_ofReal k i
  calc
    ((i • canonicalGreenJetStep k).re : ℂ) =
        (((i : ℝ) * ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
          simpa only [Complex.ofReal_re] using
            congrArg (fun z : ℂ ↦ (z.re : ℂ)) hpoint
    _ = i • canonicalGreenJetStep k := hpoint.symm

/-- On every fixed finite-difference grid, normalization of the concrete
unnormalized state is eventually exactly the separated positive state. -/
theorem completedGreenForwardDifferenceJet_normalizedConcrete_eventuallyEq_positive
    (order : ℕ) :
    (fun k ↦ completedGreenForwardDifferenceJet
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        canonicalCompletedC3ConcreteRealAxisGreenState)
      (canonicalGreenJetStep k) order) =ᶠ[Filter.atTop]
    (fun k ↦ completedGreenForwardDifferenceJet
      canonicalCompletedC3RealAxisPositiveState
      (canonicalGreenJetStep k) order) := by
  have hsamples : ∀ᶠ k : ℕ in Filter.atTop,
      ∀ i ∈ Finset.range (order + 1),
        completedNativeOperatorCharacteristic
          (i • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro i hi
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero i
  filter_upwards [hsamples] with k hk
  unfold completedGreenForwardDifferenceJet
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift,
    completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact normalizedCanonicalCompletedC3ConcreteRealAxisGreenState_eq _ (hk i hi)

/-- Parity packaging of the same eventual exact normalization. -/
theorem completedGreenForwardDifferenceParityJet_normalizedConcrete_eventuallyEq_positive
    (i : ℕ ⊕ ℕ) :
    (fun k ↦ completedGreenForwardDifferenceParityJet
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        canonicalCompletedC3ConcreteRealAxisGreenState) k i) =ᶠ[Filter.atTop]
    (fun k ↦ completedGreenForwardDifferenceParityJet
      canonicalCompletedC3RealAxisPositiveState k i) := by
  cases i with
  | inl n =>
      exact
        completedGreenForwardDifferenceJet_normalizedConcrete_eventuallyEq_positive
          (2 * n)
  | inr n =>
      exact
        completedGreenForwardDifferenceJet_normalizedConcrete_eventuallyEq_positive
          (2 * n + 1)

/-! ## Coordinate limits in the logarithmic orbit -/

/-- The finite coefficient theorem specializes to every ordinary completed
slope coordinate.  The cutoff is chosen only to expose that coordinate; no
cutoff-limit argument enters. -/
theorem completedGreenForwardDifferenceParityJet_positiveDirichletGradient_tendsto
    (n : ℕ) (i : ℕ ⊕ ℕ) :
    Filter.Tendsto
      (fun k ↦ completedGreenForwardDifferenceParityJet
        (fun z ↦ positiveDirichletGradient (operatorHeightParameter z) n)
        k i)
      Filter.atTop
      (nhds (nativeDirichletSlopeTaylorCoefficient
        (completedGreenParityOrder i) n)) := by
  let coordinate : Fin
      (NativeCarrySpectralWeyl.Limits.finiteCameraWindow 2 n + 1) :=
    ⟨n, by simp; omega⟩
  have hlimit :=
    canonicalCompletedC3DirichletGradientCoefficientParityJet_apply_tendsto
      2 n coordinate i
  apply hlimit.congr'
  filter_upwards with k
  cases i with
  | inl parityOrder =>
      simp only [canonicalCompletedC3DirichletGradientCoefficientParityJet,
        completedGreenForwardDifferenceParityJet]
      rw [completedGreenForwardDifferenceJet_apply]
      rfl
  | inr parityOrder =>
      simp only [canonicalCompletedC3DirichletGradientCoefficientParityJet,
        completedGreenForwardDifferenceParityJet]
      rw [completedGreenForwardDifferenceJet_apply]
      rfl

/-- Taylor coefficient of one logarithmically weighted Dirichlet slope. -/
def nativeLogDirichletSlopeTaylorCoefficient (order n : ℕ) : ℂ :=
  (Real.log ((n + 2 : ℕ) : ℝ) : ℂ) *
      nativeCriticalDirichletAmplitude (n + 2) *
        (-Complex.I * (Real.log ((n + 2 : ℕ) : ℝ) : ℂ)) ^ order /
          (order.factorial : ℂ) -
    (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) *
      nativeCriticalDirichletAmplitude (n + 1) *
        (-Complex.I * (Real.log ((n + 1 : ℕ) : ℝ) : ℂ)) ^ order /
          (order.factorial : ℂ)

/-- Exact forward-difference limit of every logarithmically weighted
Dirichlet atom. -/
theorem completedGreenForwardDifferenceJet_logNatDirichletTerm_tendsto
    {m : ℕ} (hm : 0 < m) (order : ℕ) :
    Filter.Tendsto
      (fun k ↦ completedGreenForwardDifferenceJet
        (fun z ↦ (Real.log (m : ℝ) : ℂ) *
          natDirichletTerm (operatorHeightParameter z) m)
        (canonicalGreenJetStep k) order)
      Filter.atTop
      (nhds ((Real.log (m : ℝ) : ℂ) *
        (nativeCriticalDirichletAmplitude m *
          (-Complex.I * (Real.log (m : ℝ) : ℂ)) ^ order /
            (order.factorial : ℂ)))) := by
  have hlimit :=
    (completedGreenForwardDifferenceJet_natDirichletTerm_tendsto hm order).const_mul
      (Real.log (m : ℝ) : ℂ)
  apply hlimit.congr'
  filter_upwards with k
  simpa only [LinearMap.mulLeft_apply] using
    (completedGreenForwardDifferenceJet_linearMap
      (LinearMap.mulLeft ℂ (Real.log (m : ℝ) : ℂ))
      (fun z ↦ natDirichletTerm (operatorHeightParameter z) m)
      (canonicalGreenJetStep k) order).symm

/-- Every completed log-jet slope coordinate has its exact logarithmic-orbit
Taylor coefficient. -/
theorem completedGreenForwardDifferenceParityJet_positiveLogDirichletGradient_tendsto
    (n : ℕ) (i : ℕ ⊕ ℕ) :
    Filter.Tendsto
      (fun k ↦ completedGreenForwardDifferenceParityJet
        (fun z ↦ positiveLogDirichletGradient (operatorHeightParameter z) n)
        k i)
      Filter.atTop
      (nhds (nativeLogDirichletSlopeTaylorCoefficient
        (completedGreenParityOrder i) n)) := by
  let order := completedGreenParityOrder i
  have hleft := completedGreenForwardDifferenceJet_logNatDirichletTerm_tendsto
    (m := n + 2) (by omega) order
  have hright := completedGreenForwardDifferenceJet_logNatDirichletTerm_tendsto
    (m := n + 1) (by omega) order
  have hsub := hleft.sub hright
  cases i with
  | inl parityOrder =>
      dsimp [order, completedGreenParityOrder] at hsub
      change Filter.Tendsto
        (fun k ↦ completedGreenForwardDifferenceJet
          (fun z ↦ positiveLogDirichletGradient (operatorHeightParameter z) n)
          (canonicalGreenJetStep k) (2 * parityOrder))
        Filter.atTop
        (nhds (nativeLogDirichletSlopeTaylorCoefficient
          (2 * parityOrder) n))
      convert hsub using 1
      · funext k
        simp only [positiveLogDirichletGradient,
          positiveLogDirichletValue,
          positiveDirichletValue_eq_natDirichletTerm]
        exact completedGreenForwardDifferenceJet_sub
          (fun z ↦ (Real.log ((n + 2 : ℕ) : ℝ) : ℂ) *
            natDirichletTerm (operatorHeightParameter z) (n + 2))
          (fun z ↦ (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) *
            natDirichletTerm (operatorHeightParameter z) (n + 1))
          (canonicalGreenJetStep k) (2 * parityOrder)
      · unfold nativeLogDirichletSlopeTaylorCoefficient
        ring
  | inr parityOrder =>
      dsimp [order, completedGreenParityOrder] at hsub
      change Filter.Tendsto
        (fun k ↦ completedGreenForwardDifferenceJet
          (fun z ↦ positiveLogDirichletGradient (operatorHeightParameter z) n)
          (canonicalGreenJetStep k) (2 * parityOrder + 1))
        Filter.atTop
        (nhds (nativeLogDirichletSlopeTaylorCoefficient
          (2 * parityOrder + 1) n))
      convert hsub using 1
      · funext k
        simp only [positiveLogDirichletGradient,
          positiveLogDirichletValue,
          positiveDirichletValue_eq_natDirichletTerm]
        exact completedGreenForwardDifferenceJet_sub
          (fun z ↦ (Real.log ((n + 2 : ℕ) : ℝ) : ℂ) *
            natDirichletTerm (operatorHeightParameter z) (n + 2))
          (fun z ↦ (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) *
            natDirichletTerm (operatorHeightParameter z) (n + 1))
          (canonicalGreenJetStep k) (2 * parityOrder + 1)
      · unfold nativeLogDirichletSlopeTaylorCoefficient
        ring

/-! ## Exact readout of the completed vector jets -/

/-- The ordinary coordinate readout of every finite positive-state jet is the
corresponding coefficient jet on the logarithmic orbit. -/
theorem canonicalCompletedC3OrdinarySlopeCoordinateReadout_positiveParityJet
    (n k : ℕ) (i : ℕ ⊕ ℕ) :
    canonicalCompletedC3OrdinarySlopeCoordinateReadout n
        (completedGreenForwardDifferenceParityJet
          canonicalCompletedC3RealAxisPositiveState k i) =
      completedGreenForwardDifferenceParityJet
        (fun z ↦ positiveDirichletGradient (operatorHeightParameter z) n)
        k i := by
  change (canonicalCompletedC3OrdinarySlopeCoordinateReadout n).toLinearMap
      (completedGreenForwardDifferenceParityJet
        canonicalCompletedC3RealAxisPositiveState k i) = _
  rw [← completedGreenForwardDifferenceParityJet_linearMap
    (canonicalCompletedC3OrdinarySlopeCoordinateReadout n).toLinearMap
    canonicalCompletedC3RealAxisPositiveState k i]
  cases i with
  | inl order =>
      simp only [completedGreenForwardDifferenceParityJet]
      rw [show (fun z ↦
          (canonicalCompletedC3OrdinarySlopeCoordinateReadout n).toLinearMap
            (canonicalCompletedC3RealAxisPositiveState z)) =
          (fun z ↦ positiveDirichletGradient
            (operatorHeightParameter (z.re : ℂ)) n) by
        funext z
        exact canonicalCompletedC3OrdinarySlopeCoordinateReadout_positiveState n z]
      exact completedGreenForwardDifferenceJet_realAxisRestriction
        (fun z ↦ positiveDirichletGradient (operatorHeightParameter z) n)
        k (2 * order)
  | inr order =>
      simp only [completedGreenForwardDifferenceParityJet]
      rw [show (fun z ↦
          (canonicalCompletedC3OrdinarySlopeCoordinateReadout n).toLinearMap
            (canonicalCompletedC3RealAxisPositiveState z)) =
          (fun z ↦ positiveDirichletGradient
            (operatorHeightParameter (z.re : ℂ)) n) by
        funext z
        exact canonicalCompletedC3OrdinarySlopeCoordinateReadout_positiveState n z]
      exact completedGreenForwardDifferenceJet_realAxisRestriction
        (fun z ↦ positiveDirichletGradient (operatorHeightParameter z) n)
        k (2 * order + 1)

/-- The log-jet coordinate readout of every finite positive-state jet is the
corresponding logarithmically weighted coefficient jet. -/
theorem canonicalCompletedC3LogJetSlopeCoordinateReadout_positiveParityJet
    (n k : ℕ) (i : ℕ ⊕ ℕ) :
    canonicalCompletedC3LogJetSlopeCoordinateReadout n
        (completedGreenForwardDifferenceParityJet
          canonicalCompletedC3RealAxisPositiveState k i) =
      completedGreenForwardDifferenceParityJet
        (fun z ↦ positiveLogDirichletGradient (operatorHeightParameter z) n)
        k i := by
  change (canonicalCompletedC3LogJetSlopeCoordinateReadout n).toLinearMap
      (completedGreenForwardDifferenceParityJet
        canonicalCompletedC3RealAxisPositiveState k i) = _
  rw [← completedGreenForwardDifferenceParityJet_linearMap
    (canonicalCompletedC3LogJetSlopeCoordinateReadout n).toLinearMap
    canonicalCompletedC3RealAxisPositiveState k i]
  cases i with
  | inl order =>
      simp only [completedGreenForwardDifferenceParityJet]
      rw [show (fun z ↦
          (canonicalCompletedC3LogJetSlopeCoordinateReadout n).toLinearMap
            (canonicalCompletedC3RealAxisPositiveState z)) =
          (fun z ↦ positiveLogDirichletGradient
            (operatorHeightParameter (z.re : ℂ)) n) by
        funext z
        exact canonicalCompletedC3LogJetSlopeCoordinateReadout_positiveState n z]
      exact completedGreenForwardDifferenceJet_realAxisRestriction
        (fun z ↦ positiveLogDirichletGradient (operatorHeightParameter z) n)
        k (2 * order)
  | inr order =>
      simp only [completedGreenForwardDifferenceParityJet]
      rw [show (fun z ↦
          (canonicalCompletedC3LogJetSlopeCoordinateReadout n).toLinearMap
            (canonicalCompletedC3RealAxisPositiveState z)) =
          (fun z ↦ positiveLogDirichletGradient
            (operatorHeightParameter (z.re : ℂ)) n) by
        funext z
        exact canonicalCompletedC3LogJetSlopeCoordinateReadout_positiveState n z]
      exact completedGreenForwardDifferenceJet_realAxisRestriction
        (fun z ↦ positiveLogDirichletGradient (operatorHeightParameter z) n)
        k (2 * order + 1)

/-- The ordinary channel reads the exact logarithmic-orbit coefficient from
every completed limit vector. -/
theorem canonicalCompletedC3OrdinarySlopeCoordinateReadout_limitParityJet
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState)
    (n : ℕ) (i : ℕ ⊕ ℕ) :
    canonicalCompletedC3OrdinarySlopeCoordinateReadout n
        (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          canonicalCompletedC3ConcreteRealAxisGreenState hkernel i) =
      nativeDirichletSlopeTaylorCoefficient
        (completedGreenParityOrder i) n := by
  have hvector :=
    completedGreenForwardDifferenceParityJet_tendsto_canonicalNativeLimit
      canonicalCompletedC3ConcreteRealAxisGreenState hkernel i
  have hread :=
    (canonicalCompletedC3OrdinarySlopeCoordinateReadout n).continuous.continuousAt.tendsto.comp
      hvector
  have hnormalize :=
    completedGreenForwardDifferenceParityJet_normalizedConcrete_eventuallyEq_positive i
  have hpositive : Filter.Tendsto
      (fun k ↦ canonicalCompletedC3OrdinarySlopeCoordinateReadout n
        (completedGreenForwardDifferenceParityJet
          canonicalCompletedC3RealAxisPositiveState k i))
      Filter.atTop
      (nhds (nativeDirichletSlopeTaylorCoefficient
        (completedGreenParityOrder i) n)) := by
    apply (completedGreenForwardDifferenceParityJet_positiveDirichletGradient_tendsto
      n i).congr'
    filter_upwards with k
    exact (canonicalCompletedC3OrdinarySlopeCoordinateReadout_positiveParityJet
      n k i).symm
  have hreadPositive := hread.congr'
    (hnormalize.fun_comp
      (canonicalCompletedC3OrdinarySlopeCoordinateReadout n))
  exact tendsto_nhds_unique hreadPositive hpositive

/-- The logarithmic channel reads its exact logarithmically weighted
coefficient from every completed limit vector. -/
theorem canonicalCompletedC3LogJetSlopeCoordinateReadout_limitParityJet
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState)
    (n : ℕ) (i : ℕ ⊕ ℕ) :
    canonicalCompletedC3LogJetSlopeCoordinateReadout n
        (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          canonicalCompletedC3ConcreteRealAxisGreenState hkernel i) =
      nativeLogDirichletSlopeTaylorCoefficient
        (completedGreenParityOrder i) n := by
  have hvector :=
    completedGreenForwardDifferenceParityJet_tendsto_canonicalNativeLimit
      canonicalCompletedC3ConcreteRealAxisGreenState hkernel i
  have hread :=
    (canonicalCompletedC3LogJetSlopeCoordinateReadout n).continuous.continuousAt.tendsto.comp
      hvector
  have hnormalize :=
    completedGreenForwardDifferenceParityJet_normalizedConcrete_eventuallyEq_positive i
  have hpositive : Filter.Tendsto
      (fun k ↦ canonicalCompletedC3LogJetSlopeCoordinateReadout n
        (completedGreenForwardDifferenceParityJet
          canonicalCompletedC3RealAxisPositiveState k i))
      Filter.atTop
      (nhds (nativeLogDirichletSlopeTaylorCoefficient
        (completedGreenParityOrder i) n)) := by
    apply (completedGreenForwardDifferenceParityJet_positiveLogDirichletGradient_tendsto
      n i).congr'
    filter_upwards with k
    exact (canonicalCompletedC3LogJetSlopeCoordinateReadout_positiveParityJet
      n k i).symm
  have hreadPositive := hread.congr'
    (hnormalize.fun_comp
      (canonicalCompletedC3LogJetSlopeCoordinateReadout n))
  exact tendsto_nhds_unique hreadPositive hpositive

/-! ## Exact Vandermonde images of the completed parity families -/

/-- Nonzero order-dependent scalar read by the ordinary odd channel. -/
def nativeOrdinaryOddJetScale (order : ℕ) : ℂ :=
  (-Complex.I) ^ (2 * order + 1) /
    ((2 * order + 1).factorial : ℂ)

/-- Nonzero order-dependent scalar read by the logarithmic even channel. -/
def nativeLogJetEvenScale (order : ℕ) : ℂ :=
  (-Complex.I) ^ (2 * order) /
    ((2 * order).factorial : ℂ)

theorem nativeOrdinaryOddJetScale_ne_zero (order : ℕ) :
    nativeOrdinaryOddJetScale order ≠ 0 := by
  unfold nativeOrdinaryOddJetScale
  exact div_ne_zero (pow_ne_zero _ (by simp))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

theorem nativeLogJetEvenScale_ne_zero (order : ℕ) :
    nativeLogJetEvenScale order ≠ 0 := by
  unfold nativeLogJetEvenScale
  exact div_ne_zero (pow_ne_zero _ (by simp))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- Odd ordinary Taylor coefficients are exactly the common Vandermonde
family, with a nonzero scalar depending only on the derivative order. -/
theorem nativeDirichletSlopeTaylorCoefficient_odd_eq
    (order n : ℕ) :
    nativeDirichletSlopeTaylorCoefficient (2 * order + 1) n =
      nativeOrdinaryOddJetScale order * nativeOddLogPowerSlopeJet order n := by
  unfold nativeDirichletSlopeTaylorCoefficient nativeOrdinaryOddJetScale
    nativeOddLogPowerSlopeJet
  simp only [mul_pow]
  ring

/-- Even logarithmic Taylor coefficients are the same common Vandermonde
family, again with a nonzero order scalar. -/
theorem nativeLogDirichletSlopeTaylorCoefficient_even_eq
    (order n : ℕ) :
    nativeLogDirichletSlopeTaylorCoefficient (2 * order) n =
      nativeLogJetEvenScale order * nativeOddLogPowerSlopeJet order n := by
  unfold nativeLogDirichletSlopeTaylorCoefficient nativeLogJetEvenScale
    nativeOddLogPowerSlopeJet
  simp only [mul_pow]
  ring

/-- Simultaneous ordinary-slope coordinate readout. -/
def canonicalCompletedC3OrdinarySlopeReadout :
    CanonicalCompletedC3RealAxisPositiveCarrier →ₗ[ℂ] (ℕ → ℂ) where
  toFun state n := canonicalCompletedC3OrdinarySlopeCoordinateReadout n state
  map_add' x y := by
    funext n
    exact (canonicalCompletedC3OrdinarySlopeCoordinateReadout n).map_add x y
  map_smul' c x := by
    funext n
    exact (canonicalCompletedC3OrdinarySlopeCoordinateReadout n).map_smul c x

/-- Simultaneous logarithmic-slope coordinate readout. -/
def canonicalCompletedC3LogJetSlopeReadout :
    CanonicalCompletedC3RealAxisPositiveCarrier →ₗ[ℂ] (ℕ → ℂ) where
  toFun state n := canonicalCompletedC3LogJetSlopeCoordinateReadout n state
  map_add' x y := by
    funext n
    exact (canonicalCompletedC3LogJetSlopeCoordinateReadout n).map_add x y
  map_smul' c x := by
    funext n
    exact (canonicalCompletedC3LogJetSlopeCoordinateReadout n).map_smul c x

/-- The odd completed limit family maps exactly to a nonzero rescaling of the
logarithmic Vandermonde slope family. -/
theorem canonicalCompletedC3OrdinarySlopeReadout_limitOdd
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState)
    (order : ℕ) :
    canonicalCompletedC3OrdinarySlopeReadout
        (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          canonicalCompletedC3ConcreteRealAxisGreenState hkernel
          (Sum.inr order)) =
      nativeOrdinaryOddJetScale order • nativeOddLogPowerSlopeJet order := by
  funext n
  change canonicalCompletedC3OrdinarySlopeCoordinateReadout n
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        canonicalCompletedC3ConcreteRealAxisGreenState hkernel
        (Sum.inr order)) = _
  rw [canonicalCompletedC3OrdinarySlopeCoordinateReadout_limitParityJet]
  change nativeDirichletSlopeTaylorCoefficient (2 * order + 1) n =
    nativeOrdinaryOddJetScale order * nativeOddLogPowerSlopeJet order n
  exact nativeDirichletSlopeTaylorCoefficient_odd_eq order n

/-- The even completed limit family maps through the retained log-jet channel
to a nonzero rescaling of the same logarithmic Vandermonde family. -/
theorem canonicalCompletedC3LogJetSlopeReadout_limitEven
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState)
    (order : ℕ) :
    canonicalCompletedC3LogJetSlopeReadout
        (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          canonicalCompletedC3ConcreteRealAxisGreenState hkernel
          (Sum.inl order)) =
      nativeLogJetEvenScale order • nativeOddLogPowerSlopeJet order := by
  funext n
  change canonicalCompletedC3LogJetSlopeCoordinateReadout n
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        canonicalCompletedC3ConcreteRealAxisGreenState hkernel
        (Sum.inl order)) = _
  rw [canonicalCompletedC3LogJetSlopeCoordinateReadout_limitParityJet]
  change nativeLogDirichletSlopeTaylorCoefficient (2 * order) n =
    nativeLogJetEvenScale order * nativeOddLogPowerSlopeJet order n
  exact nativeLogDirichletSlopeTaylorCoefficient_even_eq order n

/-- Complex-linear independence of the concrete completed odd jets follows
from their exact ordinary-channel Vandermonde image. -/
theorem canonicalCompletedNativeConcreteLimitOdd_linearIndependent_complex
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState) :
    LinearIndependent ℂ (fun n : ℕ ↦
      canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        canonicalCompletedC3ConcreteRealAxisGreenState hkernel (Sum.inr n)) := by
  let scaleUnit : ℕ → ℂˣ := fun n ↦
    Units.mk0 (nativeOrdinaryOddJetScale n)
      (nativeOrdinaryOddJetScale_ne_zero n)
  have hscaled : LinearIndependent ℂ
      (fun n : ℕ ↦ nativeOrdinaryOddJetScale n •
        nativeOddLogPowerSlopeJet n) := by
    have hunit :=
      nativeOddLogPowerSlopeJet_linearIndependent.units_smul scaleUnit
    change LinearIndependent ℂ
      (fun n : ℕ ↦ (scaleUnit n : ℂ) • nativeOddLogPowerSlopeJet n) at hunit
    simpa only [scaleUnit, Units.val_mk0] using hunit
  apply LinearIndependent.of_comp canonicalCompletedC3OrdinarySlopeReadout
  have himage :
      canonicalCompletedC3OrdinarySlopeReadout ∘
          (fun n : ℕ ↦
            canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
              canonicalCompletedC3ConcreteRealAxisGreenState hkernel (Sum.inr n)) =
        fun n : ℕ ↦ nativeOrdinaryOddJetScale n •
          nativeOddLogPowerSlopeJet n := by
    funext n
    exact canonicalCompletedC3OrdinarySlopeReadout_limitOdd hkernel n
  rw [himage]
  exact hscaled

/-- Complex-linear independence of the concrete completed even jets follows
from their exact retained log-jet Vandermonde image. -/
theorem canonicalCompletedNativeConcreteLimitEven_linearIndependent_complex
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState) :
    LinearIndependent ℂ (fun n : ℕ ↦
      canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        canonicalCompletedC3ConcreteRealAxisGreenState hkernel (Sum.inl n)) := by
  let scaleUnit : ℕ → ℂˣ := fun n ↦
    Units.mk0 (nativeLogJetEvenScale n)
      (nativeLogJetEvenScale_ne_zero n)
  have hscaled : LinearIndependent ℂ
      (fun n : ℕ ↦ nativeLogJetEvenScale n •
        nativeOddLogPowerSlopeJet n) := by
    have hunit :=
      nativeOddLogPowerSlopeJet_linearIndependent.units_smul scaleUnit
    change LinearIndependent ℂ
      (fun n : ℕ ↦ (scaleUnit n : ℂ) • nativeOddLogPowerSlopeJet n) at hunit
    simpa only [scaleUnit, Units.val_mk0] using hunit
  apply LinearIndependent.of_comp canonicalCompletedC3LogJetSlopeReadout
  have himage :
      canonicalCompletedC3LogJetSlopeReadout ∘
          (fun n : ℕ ↦
            canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
              canonicalCompletedC3ConcreteRealAxisGreenState hkernel (Sum.inl n)) =
        fun n : ℕ ↦ nativeLogJetEvenScale n •
          nativeOddLogPowerSlopeJet n := by
    funext n
    exact canonicalCompletedC3LogJetSlopeReadout_limitEven hkernel n
  rw [himage]
  exact hscaled

/-! ## Direct carrier-correct HP certificate -/

/-- Real-linear independence of the odd completed jets, obtained by scalar
restriction from the stronger complex-linear result. -/
theorem canonicalCompletedNativeConcreteLimitOdd_linearIndependent_real
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState) :
    LinearIndependent ℝ (fun n : ℕ ↦
      canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        canonicalCompletedC3ConcreteRealAxisGreenState hkernel (Sum.inr n)) :=
  (canonicalCompletedNativeConcreteLimitOdd_linearIndependent_complex
    hkernel).restrict_scalars' ℝ

/-- Real-linear independence of the even completed jets, read through the
retained logarithmic channel. -/
theorem canonicalCompletedNativeConcreteLimitEven_linearIndependent_real
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState) :
    LinearIndependent ℝ (fun n : ℕ ↦
      canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        canonicalCompletedC3ConcreteRealAxisGreenState hkernel (Sum.inl n)) :=
  (canonicalCompletedNativeConcreteLimitEven_linearIndependent_complex
    hkernel).restrict_scalars' ℝ

/-- Direct HP certificate for the concrete all-bases completed carrier.  Its
moment kernel is the proved bivariate `dslope` limit; both independence fields
come from exact finite coordinate readouts of the ordinary and log-jet
channels.  No fixed-camera incidence transport occurs. -/
theorem completedNativeRealHPCarrierCertificate_of_concreteC3Kernel
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState) :
    letI : InnerProductSpace ℝ CanonicalCompletedC3RealAxisPositiveCarrier :=
      InnerProductSpace.rclikeToReal ℂ
        CanonicalCompletedC3RealAxisPositiveCarrier
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        canonicalCompletedC3ConcreteRealAxisGreenState hkernel) := by
  letI : InnerProductSpace ℝ CanonicalCompletedC3RealAxisPositiveCarrier :=
    InnerProductSpace.rclikeToReal ℂ
      CanonicalCompletedC3RealAxisPositiveCarrier
  exact
    { momentKernel :=
        canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
          canonicalCompletedC3ConcreteRealAxisGreenState hkernel
      evenIndependent :=
        canonicalCompletedNativeConcreteLimitEven_linearIndependent_real hkernel
      oddIndependent :=
        canonicalCompletedNativeConcreteLimitOdd_linearIndependent_real hkernel }

/-- Existing concrete C3 sewing supplies the kernel input and therefore the
direct HP certificate without an auxiliary base/radius interface. -/
theorem completedNativeRealHPCarrierCertificate_of_concreteC3Sewing
    (hsewing : CanonicalCompletedC3ConcreteRealAxisPositiveSewing) :
    let hkernel :=
      hasCompletedNativeRealAxisNormalizedGreenKernel_of_concreteC3Sewing hsewing
    letI : InnerProductSpace ℝ CanonicalCompletedC3RealAxisPositiveCarrier :=
      InnerProductSpace.rclikeToReal ℂ
        CanonicalCompletedC3RealAxisPositiveCarrier
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        canonicalCompletedC3ConcreteRealAxisGreenState hkernel) := by
  dsimp only
  exact completedNativeRealHPCarrierCertificate_of_concreteC3Kernel
    (hasCompletedNativeRealAxisNormalizedGreenKernel_of_concreteC3Sewing hsewing)

/-- End-to-end test: the direct certificate is consumed by the already proved
positive-Jacobi resolvent confinement theorem. -/
theorem completedNativeOperator_zero_im_eq_zero_of_concreteC3Kernel
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 := by
  letI : InnerProductSpace ℝ CanonicalCompletedC3RealAxisPositiveCarrier :=
    InnerProductSpace.rclikeToReal ℂ
      CanonicalCompletedC3RealAxisPositiveCarrier
  exact
    CompletedNativeRealHPCarrierCertificate.completedNativeOperator_zero_im_eq_zero_of_positiveJacobiResolvent
        (completedNativeRealHPCarrierCertificate_of_concreteC3Kernel hkernel)
        hzDomain hzero

/-- Sewing-form specialization of the same end-to-end confinement theorem. -/
theorem completedNativeOperator_zero_im_eq_zero_of_concreteC3Sewing
    (hsewing : CanonicalCompletedC3ConcreteRealAxisPositiveSewing)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_concreteC3Kernel
    (hasCompletedNativeRealAxisNormalizedGreenKernel_of_concreteC3Sewing hsewing)
    hzDomain hzero

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.C3ProjectiveHilbertRBBridge
import CarrySelfAdjointOperator.NativeMomentProjectiveValveBridge
import CarrySelfAdjointOperator.PositiveObservableNativeMomentBridge
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CPFormal.Analytic.CpGenuineFirstCutoffTail
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The completed projective Hilbert kernel and its native scalar readout

The same recovered weighted state has a positive polarized Hilbert kernel and
an exact head-plus-tail characteristic readout. We construct both, preserve
their provenance, and connect the readout's even coefficient series with the
native reciprocal valve mass. The raw Hilbert kernel is not silently equated
with the logarithmic-moment kernel: its unit seed already forces a different
central normalization.
-/

open scoped BigOperators Topology RealInnerProductSpace InnerProductSpace lp ENNReal NNReal ComplexOrder
namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open Filter PowerSeries ProjectiveValve

noncomputable section

/-- Completed Hilbert pairing after the faithful projective analysis. -/
def completedProjectiveHilbertKernel
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t u : ℝ) : ℂ :=
  nativeGpreTfvdProjectivePulledBackInner q hq0 hq1
    (nativeGpreTfvdProjectiveHilbertRealization q
      (nativeCarryWeightedRealSpectralState q hq0 hq1 t))
    (nativeGpreTfvdProjectiveHilbertRealization q
      (nativeCarryWeightedRealSpectralState q hq0 hq1 u))

/-- The projective metric retains every complex cross term. -/
theorem completedProjectiveHilbertKernel_eq_inner
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (t u : ℝ) :
    completedProjectiveHilbertKernel q hqpos.le hq1 t u =
      inner ℂ (nativeCarryWeightedRealSpectralState q hqpos.le hq1 t)
        (nativeCarryWeightedRealSpectralState q hqpos.le hq1 u) := by
  exact nativeGpreTfvdProjectivePulledBackInner_realization q hqpos hq1 _ _

/-- Every finite section of the completed kernel is positive semidefinite. -/
theorem completedProjectiveHilbertKernel_finiteSection_posSemidef
    {ι : Type*} [Fintype ι]
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (time : ι → ℝ) :
    Matrix.PosSemidef (fun i j => completedProjectiveHilbertKernel q hqpos.le hq1
      (time i) (time j)) := by
  simp_rw [completedProjectiveHilbertKernel_eq_inner q hqpos hq1]
  exact Matrix.posSemidef_gram ℂ
    (fun i : ι => nativeCarryWeightedRealSpectralState q hqpos.le hq1 (time i))

/-- Strong state completion preserves the polarized kernel, not just norms. -/
theorem finiteWeightedState_inner_tendsto_completedProjectiveHilbertKernel
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (t u : ℝ) :
    Tendsto
      (fun M : ℕ =>
        inner ℂ (nativeGpreFiniteWeightedRealSpectralState q M t)
          (nativeGpreFiniteWeightedRealSpectralState q M u))
      atTop (nhds (completedProjectiveHilbertKernel q hqpos.le hq1 t u)) := by
  rw [completedProjectiveHilbertKernel_eq_inner q hqpos hq1]
  exact (nativeGpreFiniteWeightedRealSpectralState_tendsto q hqpos.le hq1 t).inner
    (nativeGpreFiniteWeightedRealSpectralState_tendsto q hqpos.le hq1 u)

/-- The initial unit seed is retained by this full Hilbert realization. -/
theorem one_le_norm_nativeCarryWeightedRealSpectralState
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    1 ≤ ‖nativeCarryWeightedRealSpectralState q hq0 hq1 t‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (nativeCarryWeightedRealSpectralState q hq0 hq1 t) 0
  simpa using h

/-- The completed raw Hilbert kernel has diagonal mass at least one. -/
theorem one_le_completedProjectiveHilbertKernel_diagonal
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (t : ℝ) :
    1 ≤ (completedProjectiveHilbertKernel q hqpos.le hq1 t t).re := by
  rw [completedProjectiveHilbertKernel_eq_inner q hqpos hq1]
  change 1 ≤ RCLike.re (inner ℂ _ _)
  rw [inner_self_eq_norm_sq]
  have h := one_le_norm_nativeCarryWeightedRealSpectralState q hqpos.le hq1 t
  nlinarith

/-- This test concerns the raw transported metric, before any response-state
construction. It does not exclude other observables or native normalizations. -/
theorem completedProjectiveHilbertKernel_zero_ne_nativeMoment
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    (completedProjectiveHilbertKernel q hqpos.le hq1 0 0).re ≠
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hraw := one_le_completedProjectiveHilbertKernel_diagonal q hqpos hq1 0
  have hnative := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

/-- Read the finite chart only after recovering the state from the projective
TFVD data, then retain the exact analytic tail and both native dressings. -/
def completedProjectiveStateCharacteristic
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) (t : ℝ) : ℂ :=
  nativeXiCompletionFactor (t : ℂ) *
    ((carryWeightedFiniteChartObserver q M
      (nativeGpreTfvdProjectiveHilbertRecovery q hq0 hq1
        (nativeGpreTfvdProjectiveHilbertRealization q
          (nativeGpreFiniteWeightedRealSpectralState q M t))) +
      realCpBracketCutoffTail 3 M (criticalLineParameter t)) /
      cpChartFactor 3 (criticalLineParameter t))

/-- Head, exact tail, camera factor and completion factor yield the actual
native characteristic on the whole real height axis. -/
theorem completedProjectiveStateCharacteristic_eq
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (M : ℕ) :
    completedProjectiveStateCharacteristic q hqpos.le hq1 M =
      fun t : ℝ => completedNativeOperatorCharacteristic (t : ℂ) := by
  funext t
  have hs := criticalLineParameter_mem_genuineCriticalStrip t
  have htail : -1 < (criticalLineParameter t).re := by
    norm_num [criticalLineParameter]
  have hfactor := cpChartFactor_ne_zero_on_genuineCriticalStrip
    3 (by norm_num) hs
  have hparameter : operatorHeightParameter (t : ℂ) = criticalLineParameter t := by
    simp [operatorHeightParameter, criticalLineParameter, mul_comm]
  unfold completedProjectiveStateCharacteristic
    nativeGpreTfvdProjectiveHilbertRecovery
    nativeGpreTfvdProjectiveHilbertRealization
  rw [nativeGpreTfvdProjectiveReconstruction_analysis q hqpos hq1,
    carryWeightedFiniteChartObserver_finiteRealSpectralState q hqpos.ne']
  unfold finiteRealSpectralChart
  rw [← bracketedDirichletChart_eq_finite_add_cutoffTail 3 M (by norm_num) htail,
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      3 (by norm_num) (by norm_num) hs]
  rw [mul_div_cancel_left₀ _ hfactor]
  rw [completedNativeOperatorCharacteristic, hparameter,
    nativeScalar_eq_genuineContinuation_unconditional]

/-- The readout from every complete cutoff has exactly the native jets. -/
theorem iteratedDeriv_completedProjectiveStateCharacteristic
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (M order : ℕ) (t : ℝ) :
    iteratedDeriv order (completedProjectiveStateCharacteristic q hqpos.le hq1 M) t =
      iteratedDeriv order completedNativeOperatorCharacteristic (t : ℂ) := by
  rw [completedProjectiveStateCharacteristic_eq q hqpos hq1 M]
  exact iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal order t

/-- Even coefficients read from the reconstructed, completed state itself. -/
def completedProjectiveStateEvenCoefficient
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (M n : ℕ) : ℝ :=
  ((((Nat.factorial (2*n) : ℂ)⁻¹) •
    iteratedDeriv (2*n) (completedProjectiveStateCharacteristic q hq0 hq1 M) 0) : ℂ).re

theorem completedProjectiveStateEvenCoefficient_eq_native
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (M n : ℕ) :
    completedProjectiveStateEvenCoefficient q hqpos.le hq1 M n =
      completedNativeRealEvenCharacteristicCoefficient n := by
  unfold completedProjectiveStateEvenCoefficient
    completedNativeRealEvenCharacteristicCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  rw [iteratedDeriv_completedProjectiveStateCharacteristic q hqpos hq1]
  simp only [Complex.ofReal_zero]

/-- Reciprocal normalized mass formed directly from the completed readout
coefficients. This definition does not use the native moment sequence. -/
def completedProjectiveStateReciprocalMass
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) : PowerSeries ℝ :=
  (C (completedProjectiveStateEvenCoefficient q hq0 hq1 M 0)⁻¹ *
    mk (completedProjectiveStateEvenCoefficient q hq0 hq1 M))⁻¹

/-- The mass observed from the same state equals the reciprocal native
characteristic, with all normalization and completion factors retained. -/
theorem completedProjectiveStateReciprocalMass_eq_native
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (M : ℕ) :
    completedProjectiveStateReciprocalMass q hqpos.le hq1 M =
      normalizedCompletedNativeEvenFormalSeries⁻¹ := by
  unfold completedProjectiveStateReciprocalMass
  have hcoeff : completedProjectiveStateEvenCoefficient q hqpos.le hq1 M =
      completedNativeRealEvenCharacteristicCoefficient := by
    funext n
    exact completedProjectiveStateEvenCoefficient_eq_native q hqpos hq1 M n
  rw [hcoeff]
  rfl

/-- Exact scalar valve identity for the mass recovered from the weighted
Hilbert state; no Gram identification is inserted into this statement. -/
theorem completedProjectiveStateReciprocalMass_eq_valveNativeMoments
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (M : ℕ) :
    completedProjectiveStateReciprocalMass q hqpos.le hq1 M =
      projectiveValveMass (mk canonicalCompletedNativeLogDerivativeMoment) := by
  rw [completedProjectiveStateReciprocalMass_eq_native q hqpos hq1 M]
  exact projectiveValveMass_nativeMoments_eq_reciprocal.symm


/-- The observable's remaining moment obligation can be checked against the
actual completed readout mass, without introducing a second target series. -/
theorem positiveObservable_isNativeMomentSequence_iff_completedProjectiveReadoutMass
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : H →L[ℝ] H) (u : H)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (M : ℕ) :
    IsCompletedNativeLogDerivativeMomentSequence (positiveObservableMoment S u) ↔
      projectiveValveMass (mk (positiveObservableMoment S u)) =
        completedProjectiveStateReciprocalMass q hqpos.le hq1 M := by
  rw [completedProjectiveStateReciprocalMass_eq_native q hqpos hq1 M]
  exact isNativeMomentSequence_iff_valveMass_eq_nativeReciprocal _

/-- Conditional endpoint for a constructed symmetric observable and source.
The mass equality and cyclic independence are explicit inputs, not consequences
of scalar reconstruction or of the raw completed Hilbert kernel. -/
theorem completedNativeRealHPCarrierCertificate_of_positiveObservable_readoutMass
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric) (u : H)
    (hcyclic : LinearIndependent ℝ (positiveObservableOrbit S u))
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (M : ℕ)
    (hmass : projectiveValveMass (mk (positiveObservableMoment S u)) =
      completedProjectiveStateReciprocalMass q hqpos.le hq1 M) :
    CompletedNativeRealHPCarrierCertificate (positiveObservableParityJet S u) := by
  have hm := (positiveObservable_isNativeMomentSequence_iff_completedProjectiveReadoutMass
    S u q hqpos hq1 M).2 hmass
  exact completedNativeRealHPCarrierCertificate_of_positiveObservable S hS u hcyclic
    ((positiveObservable_isNativeMomentSequence_iff_defect_zero S u).1 hm)

end
end CarrySelfAdjointOperator

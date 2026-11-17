import CarrySelfAdjointOperator.C2GlobalGreenBridge
import CarrySelfAdjointOperator.PositiveObservableNativeMomentBridge
import CarrySelfAdjointOperator.CompletedNativeAllOrderMomentUpperBound
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CarrySelfAdjointOperator.CompletedNativeTaylorResidualNoGo
import CarrySelfAdjointOperator.CompletedNativeChiralBoundaryJetTransport
import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundaryStieltjesGate

/-!
# Low-order tests before identifying a critical branch with the native kernel

The strict obstruction concerns the UNCHANGED unit source. It does not assert
that the material-clock compression complement has unit mass. The latter must
be compared to the signed boundary through an independent polarized sewing.
-/
namespace CarrySelfAdjointOperator.CriticalBranchNativeAudit
open scoped BigOperators
open GeometryOfNumbers.Analysis
noncomputable section
set_option autoImplicit false

/-- The first original boundary face has its inherited factor FOUR and
both canonical sectors. This test does not replace the signed finite steps. -/
theorem native_boundary_two (x : Fin 2 → ℂ) :
    nativeSourceFiniteBoundaryEnergy 2 x = 4 *
      (canonicalCompletedNativeLogDerivativeMoment 0 * Complex.normSq (x 0) +
       canonicalCompletedNativeLogDerivativeMoment 1 * Complex.normSq (x 1)) := by
  have h := nativeSourceFiniteBoundaryEnergy_even_split 1 x
  simpa [nativeSourceEvenBoundaryPhase, nativeSourceOddBoundaryPhase,
    nativeSourceEvenBoundaryIndex, nativeSourceOddBoundaryIndex,
    primeDepthGeometricMoment_eq_canonical, Complex.normSq_apply, Complex.mul_re] using h

section Observable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The complete convolution residual is the triangular transport of the
actual moment errors, with the original completed characteristic coefficients. -/
theorem convolutionDefect_eq_moment_errors (S : H →L[ℝ] H) (u : H) (n : ℕ) :
    positiveObservableNativeConvolutionDefect S u n =
      completedNativeRealEvenCharacteristicCoefficient 0 *
        (positiveObservableMoment S u n - canonicalCompletedNativeLogDerivativeMoment n) +
      ∑ k ∈ Finset.range n,
        (positiveObservableMoment S u k - canonicalCompletedNativeLogDerivativeMoment k) *
          completedNativeRealEvenCharacteristicCoefficient (n-k) := by
  have hn := canonicalCompletedNativeLogDerivativeMoment_real_recurrence n
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  unfold positiveObservableNativeConvolutionDefect
  linarith

/-- The zeroth defect calibrates the SAME source norm, before an operator
choice can affect any higher moment. -/
theorem convolutionDefect_zero_eq_mass_error (S : H →L[ℝ] H) (u : H) :
    positiveObservableNativeConvolutionDefect S u 0 =
      completedNativeRealEvenCharacteristicCoefficient 0 *
        (‖u‖^2 - canonicalCompletedNativeLogDerivativeMoment 0) := by
  rw [convolutionDefect_eq_moment_errors]
  simp [positiveObservableMoment, positiveObservableOrbit]

theorem unit_source_zero_defect_gt (S : H →L[ℝ] H) (u : H) (hu : ‖u‖ = 1) :
    (15/16 : ℝ) * completedNativeRealEvenCharacteristicCoefficient 0 <
      positiveObservableNativeConvolutionDefect S u 0 := by
  rw [convolutionDefect_zero_eq_mass_error, hu]
  have hc : 0 < completedNativeRealEvenCharacteristicCoefficient 0 := by
    have hc := completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
    linarith
  have hm := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  nlinarith

theorem unit_source_zero_defect_pos (S : H →L[ℝ] H) (u : H) (hu : ‖u‖ = 1) :
    0 < positiveObservableNativeConvolutionDefect S u 0 := by
  have hc := completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have h := unit_source_zero_defect_gt S u hu
  linarith

end Observable

/-- Literal pure C2 branch: both legs and their original amplitudes remain. -/
theorem raw_critical_branch_zero_defect_pos (t : ℝ)
    (S : C2BranchCarrier →L[ℝ] C2BranchCarrier)
    (v : RealPlaneHilbert) (hv : ‖v‖ = 1) :
    0 < positiveObservableNativeConvolutionDefect S (realCriticalBranchIsometry t v) 0 :=
  unit_source_zero_defect_pos S _ (by rw [LinearIsometry.norm_map, hv])

/-- The arithmetic incidence and physical material phase preserve the same
obstruction. This does not replace phase by branch depth. -/
theorem raw_global_physical_branch_zero_defect_pos (t : ℝ)
    (S : OddMaterialState →L[ℝ] OddMaterialState) (v : CoreState) (hv : ‖v‖ = 1) :
    0 < positiveObservableNativeConvolutionDefect S
      (globalCriticalPhysicalBranchIsometry t v) 0 :=
  unit_source_zero_defect_pos S _ (by rw [LinearIsometry.norm_map, hv])

/-- The actual local Green input also retains the original unit mass. -/
theorem raw_green_input_zero_defect_pos (t : ℝ)
    (S : GreenFrame.Concrete.State →L[ℝ] GreenFrame.Concrete.State)
    (v : CoreState) (hv : ‖v‖ = 1) :
    0 < positiveObservableNativeConvolutionDefect S
      (C2GlobalGreenBridge.c2GlobalGreenInputIsometry t v) 0 :=
  unit_source_zero_defect_pos S _ (by rw [LinearIsometry.norm_map, hv])

/-- A literal even-jet assignment to distinct raw material cores also
fails the first off-diagonal test, independently of the diagonal mismatch. -/
theorem raw_distinct_cores_even_cross_not_native (t : ℝ)
    (m l : PositiveOddCore) (hml : m ≠ l) (v w : RealPlaneHilbert) :
    inner ℝ (globalCriticalPhysicalBranchIsometry t (lp.single 2 m v))
      (globalCriticalPhysicalBranchIsometry t (lp.single 2 l w)) ≠
        canonicalCompletedNativeLogDerivativeMoment 1 := by
  rw [globalCriticalPhysicalBranch_core_orthogonal t m l hml v w]
  exact canonicalCompletedNativeLogDerivativeMoment_one_ne_zero.symm

/-- No choice of bounded real observable repairs this unchanged unit source. -/
theorem raw_global_physical_branch_not_native (t : ℝ)
    (S : OddMaterialState →L[ℝ] OddMaterialState) (v : CoreState) (hv : ‖v‖ = 1) :
    ¬ IsCompletedNativeLogDerivativeMomentSequence
      (positiveObservableMoment S (globalCriticalPhysicalBranchIsometry t v)) := by
  intro h
  have hz := (positiveObservable_isNativeMomentSequence_iff_defect_zero S _).1 h 0
  have hp := raw_global_physical_branch_zero_defect_pos t S v hv
  rw [hz] at hp
  exact (lt_irrefl 0) hp

end
end CarrySelfAdjointOperator.CriticalBranchNativeAudit

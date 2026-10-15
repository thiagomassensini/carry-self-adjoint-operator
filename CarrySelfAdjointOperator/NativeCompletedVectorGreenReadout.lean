import CarrySelfAdjointOperator.NativeCompletedDividedVectorSeries
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! The constructed vector response has the original normalized completed
Green readout. The completion connection remains present on two independent
inputs. No Gram, positivity, coisometry or moment realization is a premise. -/
namespace CarrySelfAdjointOperator.DividedVectorResponse
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary SourceKernelCalibration
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

private abbrev scalarResponse : ℂ → ℂ :=
  completedGreenNormalizedResponse completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion

theorem completedValueNormalizedGreen_eq_response_numerator (z w : ℂ)
    (hz : completedNativeOperatorCharacteristic z ≠ 0)
    (hw : completedNativeOperatorCharacteristic w ≠ 0) :
    completedValueNormalizedGreen z w =
      2*(scalarResponse w-conj (scalarResponse z)) := by
  unfold completedValueNormalizedGreen scalarResponse completedGreenNormalizedResponse
  simp only [canonicalCompletedC3ScalarBoundaryPair, greenForm, RCLike.inner_apply,
    map_div₀, map_mul, map_ofNat]
  have hzc : conj (completedNativeOperatorCharacteristic z) ≠ 0 := by simpa using hz
  field_simp

/-- Original Green denominator, original factors, and actual vector inputs.
The central value is separately supplied by response_center_readout. -/
theorem polarizedResponse_green_readout_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z w : ℂ, conj z ∈ U → w ∈ U →
        operatorHeightParameter z ∈ genuineCriticalStrip →
        completedNativeOperatorCharacteristic z ≠ 0 →
        completedNativeOperatorCharacteristic w ≠ 0 → w ≠ conj z →
        primeDepthNormalizedResponseVectorReadout (polarizedResponse z w) =
          completedValueNormalizedGreen z w/(2*(w-conj z)) := by
  rcases polarizedResponse_readout_local with ⟨U, hopen, hzero, hU⟩
  refine ⟨U, hopen, hzero, ?_⟩
  intro z w hz hw hs hFz hFw hne
  rw [hU z w hz hw hs hne,
    completedValueNormalizedGreen_eq_response_numerator z w hFz hFw]
  change (scalarResponse w-conj (scalarResponse z))/(w-conj z) = _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact completion correction of the CONSTRUCTED response, rather than
an abstract scalar kernel with an assumed vector realization. -/
theorem polarizedResponse_completion_connection_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z w : ℂ, conj z ∈ U → w ∈ U →
        operatorHeightParameter z ∈ genuineCriticalStrip →
        operatorHeightParameter w ∈ genuineCriticalStrip →
        nativeXiCompletionFactor z ≠ 0 → nativeXiCompletionFactor w ≠ 0 →
        nativeHeightScalar z ≠ 0 → nativeHeightScalar w ≠ 0 → w ≠ conj z →
        primeDepthNormalizedResponseVectorReadout (polarizedResponse z w) -
            undressedValueNormalizedGreen z w/(2*(w-conj z)) =
          (completionConnection w-conj (completionConnection z))/(2*(w-conj z)) := by
  rcases polarizedResponse_green_readout_local with ⟨U, hopen, hzero, hU⟩
  refine ⟨U, hopen, hzero, ?_⟩
  intro z w hz hw hsz hsw hAz hAw hNz hNw hne
  have hFz : completedNativeOperatorCharacteristic z ≠ 0 := mul_ne_zero hAz hNz
  have hFw : completedNativeOperatorCharacteristic w ≠ 0 := mul_ne_zero hAw hNw
  rw [hU z w hz hw hsz hFz hFw hne]
  exact dividedGreen_connection_correction z w hsz hsw hAz hAw hNz hNw

/-- Both parity sectors, and any higher shift, are read from the same
source-defined anti-diagonal vector ledger. -/
theorem coefficientVector_parity_readout (s i j : ℕ) :
    primeDepthNormalizedResponseVectorReadout (coefficientVector (2*i+s) (2*j+s)) =
      (canonicalCompletedNativeLogDerivativeMoment (i+j+s) : ℂ) := by
  rw [coefficientVector_readout]
  unfold polarizedGreenMomentCoefficient evenMomentDiagonalCoefficient
  have he : Even ((2*i+s)+(2*j+s)) := ⟨i+j+s, by omega⟩
  rw [if_pos he]
  congr 2
  omega

/-- A quadratic vector built before readout from the source response. This
is deliberately NOT the norm of a linearly synthesized moment family. -/
def parityEnergyVector (s N : ℕ) (x : Fin N → ℝ) : CompletedPrimeDepthJetCarrier :=
  ∑ i, ∑ j, ((x i*x j : ℝ) : ℂ) • coefficientVector (2*i.val+s) (2*j.val+s)

/-- The literal original source energy, at arbitrary dimension and input,
is the fixed readout of the fully crossed vector response. -/
theorem parityEnergyVector_readout (s N : ℕ) (x : Fin N → ℝ) :
    primeDepthNormalizedResponseVectorReadout (parityEnergyVector s N x) =
      (sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment s N x : ℂ) := by
  simp only [parityEnergyVector, map_sum, map_smul, smul_eq_mul,
    coefficientVector_parity_readout]
  simp only [sourceMomentQuadratic, sourceMomentMatrix, Matrix.mulVec, dotProduct,
    Pi.star_apply, star_trivial, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end CarrySelfAdjointOperator.DividedVectorResponse

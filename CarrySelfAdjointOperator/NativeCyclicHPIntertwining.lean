import CarrySelfAdjointOperator.NativeLogEvolution
import CarrySelfAdjointOperator.PositiveObservableNativeMomentBridge
import CarrySelfAdjointOperator.CompletedNativeLogDerivativeTriangularTransport
import CPFormal.Analytic.CpNativeCarryContinuousSpectrumThreshold

/-!
# Native cyclic realization: source obstruction and exact readout diagnostic

The undamped native orbit is not a vector in the logarithmic generator's
Hilbert space. The finite triangular test below applies to an independently
constructed observable and source; it does not construct either one from
moments. No native cyclic realization or unconditional HP certificate is
asserted. In the existing positive-observable API the positive coordinate is
`S * S`, and its moments are the even powers of `S`.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The coordinatewise native log orbit cannot be used unchanged as a Hilbert
cyclic source. This is a typed consequence of the existing harmonic threshold,
not an obstruction to a different, geometrically justified realization. -/
theorem nativeLogHilbert_no_undampedCyclicSource (t : ℝ) :
    ¬ ∃ x : NativeLogHilbert, ∀ n : ℕ, x n = realSpectralState t n := by
  rintro ⟨x, hx⟩
  apply not_summable_norm_sq_realSpectralState t
  have hs := (lp.memℓp x).summable (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hx] using hs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Prefix of cyclic moments of the independently supplied observable.
Neither the native characteristic nor its moments occur in this definition. -/
def nativeCyclicCandidateMomentVector
    (S : H →L[ℝ] H) (x : H) (N : ℕ) : Fin N → ℂ :=
  fun i => (positiveObservableMoment S x i.val : ℂ)

/-- Division-free prefix readout defect. Its target uses the characteristic
coefficients, not a Gram chosen to fit the candidate. -/
def nativeCyclicTriangularReadoutDefect
    (S : H →L[ℝ] H) (x : H) (N : ℕ) : Fin N → ℂ :=
  (completedNativeLogDerivativeTriangularMatrix N).mulVec
      (nativeCyclicCandidateMomentVector S x N) -
    completedNativeLogDerivativeSourceVector N

/-- The exact readout defect is the invertible triangular transport of the
moment error. This is an equality, not a vanishing assertion. -/
theorem nativeCyclicTriangularReadoutDefect_eq_transport
    (S : H →L[ℝ] H) (x : H) (N : ℕ) :
    nativeCyclicTriangularReadoutDefect S x N =
      (completedNativeLogDerivativeTriangularMatrix N).mulVec
        (nativeCyclicCandidateMomentVector S x N -
          completedNativeLogDerivativeMomentVector N) := by
  rw [Matrix.mulVec_sub, completedNativeLogDerivativeTriangularMatrix_mulVec_moments]
  rfl

/-- No loss of information in the prefix diagnostic: zero readout error is
exactly equality of the candidate and canonical moments through that prefix. -/
theorem nativeCyclicTriangularReadoutDefect_zero_iff
    (S : H →L[ℝ] H) (x : H) (N : ℕ) :
    nativeCyclicTriangularReadoutDefect S x N = 0 ↔
      ∀ i : Fin N, positiveObservableMoment S x i.val =
        canonicalCompletedNativeLogDerivativeMoment i.val := by
  unfold nativeCyclicTriangularReadoutDefect
  rw [sub_eq_zero, ← completedNativeLogDerivativeTriangularMatrix_mulVec_moments N]
  rw [(completedNativeLogDerivativeTriangularMatrix_mulVec_bijective N).1.eq_iff]
  constructor
  · intro h i
    have hi := congrFun h i
    exact Complex.ofReal_injective hi
  · intro h
    funext i
    exact congrArg Complex.ofReal (h i)

/-- All finite tests are precisely the existing scalar convolution gate.
This identifies the residual with an existing obligation, without replacing
that obligation by a new assumed kernel interface. -/
theorem nativeCyclicTriangularReadoutDefect_all_zero_iff_convolution
    (S : H →L[ℝ] H) (x : H) :
    (∀ N, nativeCyclicTriangularReadoutDefect S x N = 0) ↔
      ∀ n, positiveObservableNativeConvolutionDefect S x n = 0 := by
  constructor
  · intro h
    have hm : positiveObservableMoment S x =
        canonicalCompletedNativeLogDerivativeMoment := by
      funext n
      exact (nativeCyclicTriangularReadoutDefect_zero_iff S x (n+1)).1
        (h (n+1)) ⟨n, Nat.lt_succ_self n⟩
    apply (positiveObservable_isNativeMomentSequence_iff_defect_zero S x).1
    rw [hm]
    exact canonicalCompletedNativeLogDerivativeMoment_isMomentSequence
  · intro h N
    apply (nativeCyclicTriangularReadoutDefect_zero_iff S x N).2
    intro i
    exact congrFun (positiveObservableMoment_eq_native_of_defect_zero S x h) i.val

end
end CarrySelfAdjointOperator

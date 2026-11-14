import CarrySelfAdjointOperator.CompletedNativeCommonPoleCancellation
import CarrySelfAdjointOperator.CompletedNativeCharacteristic
import CarrySelfAdjointOperator.CompletedProductJet
import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance
import CarrySelfAdjointOperator.CompletedGreenDiagonalClosure
import NativeCarrySpectralWeyl.Camera.CrossFactorization
import NativeCarrySpectralWeyl.Camera.NativeLineFloor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# C2 native adapter for common-pole cancellation

The camera denominator below is the original exceptional camera-2 factor.
The head-plus-tail characteristic remains the exact source input; no zero
representation or spectral formula is used to define it.
-/

namespace CarrySelfAdjointOperator

open Filter
open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- The operator's `-F'/F` normalization is exactly twice the half-log
response used to isolate the common pole. -/
theorem c2CompletedNativeLogDerivative_eq_twice_halfLogResponse :
    completedNativeOperatorLogDerivative = fun z =>
      (2 : ℂ) * halfLogResponse completedNativeOperatorCharacteristic z := by
  funext z
  unfold completedNativeOperatorLogDerivative halfLogResponse
  simp only [div_eq_mul_inv]
  ring

/-- Original camera-2 denominator in the centered height variable. -/
def c2OriginalCameraDenominator (z : ℂ) : ℂ :=
  factor 2 (operatorHeightParameter z)

/-- Exact complete camera-2 bracket at the original cutoff. -/
def c2OriginalCompletedBracket (M : ℕ) (z : ℂ) : ℂ :=
  completedNativeCharacteristic 2 M (operatorHeightParameter z)

/-- The centered height parameter is entire. -/
theorem operatorHeightParameter_differentiable :
    Differentiable ℂ operatorHeightParameter := by
  intro z
  unfold operatorHeightParameter
  fun_prop

/-- The pinned camera-2 denominator is differentiable in the height chart. -/
theorem c2OriginalCameraDenominator_differentiable :
    Differentiable ℂ c2OriginalCameraDenominator := by
  unfold c2OriginalCameraDenominator
  exact (factor_differentiable (by omega : 2 ≤ 2)).comp
    operatorHeightParameter_differentiable

/-- The shared linear pole factor is entire in the height chart. -/
theorem commonPoleHeightFactor_differentiable :
    Differentiable ℂ commonPoleHeightFactor := by
  unfold commonPoleHeightFactor operatorHeightParameter
  fun_prop

/-- `factor 2` is the exceptional aligned C2 factor `c2Factor`, not the
camera-3 chart factor. -/
theorem c2OriginalCameraDenominator_eq_c2Factor (z : ℂ) :
    c2OriginalCameraDenominator z =
      c2Factor (operatorHeightParameter z) := by
  simp [c2OriginalCameraDenominator]

/-- The same pinned camera-2 denominator, in the order used in the scalar
formula `Q(s)=(1-2^(1-s))*(1+2^(-s))`. -/
theorem c2OriginalCameraDenominator_eq_original_Q (z : ℂ) :
    c2OriginalCameraDenominator z =
      (1 - (2 : ℂ) ^ (1 - operatorHeightParameter z)) *
        (1 + (2 : ℂ) ^ (-operatorHeightParameter z)) := by
  rw [c2OriginalCameraDenominator_eq_c2Factor]
  unfold c2Factor
  ring

/-- Exact cross-multiplied identity from the existing complete-head/tail
factorization and completion factorization. -/
theorem c2OriginalCompletedCharacteristic_cross
    (M : ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ nativeScalarDomain) :
    nativeXiCompletionFactor z * c2OriginalCompletedBracket M z =
      c2OriginalCameraDenominator z *
        completedNativeOperatorCharacteristic z := by
  have h := nativeXiCompletionFactor_mul_completedNativeCharacteristic
    (camera := 2) (cutoff := M) (by omega) (z := z) hs
  simpa [c2OriginalCompletedBracket, c2OriginalCameraDenominator,
    factor_two] using h

/-- The original completed source is `A * B / Q` wherever the actual C2
camera denominator is nonzero. -/
theorem c2OriginalCompletedCharacteristic_eq_completion_bracket_div_camera
    (M : ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ nativeScalarDomain)
    (hQ : c2OriginalCameraDenominator z ≠ 0) :
    completedNativeOperatorCharacteristic z =
      nativeXiCompletionFactor z * c2OriginalCompletedBracket M z /
        c2OriginalCameraDenominator z := by
  apply (eq_div_iff hQ).2
  calc
    completedNativeOperatorCharacteristic z *
        c2OriginalCameraDenominator z =
      c2OriginalCameraDenominator z *
        completedNativeOperatorCharacteristic z := by ring
    _ = nativeXiCompletionFactor z * c2OriginalCompletedBracket M z :=
      (c2OriginalCompletedCharacteristic_cross M z hs).symm

/-- Reduced archimedean factor `a=A/(s-1)` in the centered height chart. -/
def c2ReducedCompletionFactor (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z / commonPoleHeightFactor z

/-- Reduced camera-2 denominator `q=Q/(s-1)` in the centered height chart. -/
def c2ReducedCameraFactor (z : ℂ) : ℂ :=
  c2OriginalCameraDenominator z / commonPoleHeightFactor z

/-- Removing the shared factor is an exact algebraic identity in the critical
height germ; the denominator and completion remain the originals. -/
theorem c2OriginalCompletedCharacteristic_eq_reduced_critical_germ_pointwise
    (M : ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ nativeScalarDomain)
    (hX : commonPoleHeightFactor z ≠ 0)
    (hQ : c2OriginalCameraDenominator z ≠ 0) :
    completedNativeOperatorCharacteristic z =
      c2ReducedCompletionFactor z * c2OriginalCompletedBracket M z /
        c2ReducedCameraFactor z := by
  have hq : c2ReducedCameraFactor z ≠ 0 := div_ne_zero hQ hX
  rw [c2OriginalCompletedCharacteristic_eq_completion_bracket_div_camera
    M z hs hQ]
  unfold c2ReducedCompletionFactor c2ReducedCameraFactor
  field_simp [hX, hQ, hq]

/-- The shared factor is nonzero at the critical center `s=1/2`. -/
theorem commonPoleHeightFactor_zero_ne_zero :
    commonPoleHeightFactor 0 ≠ 0 := by
  rw [commonPoleHeightFactor_eq]
  norm_num

/-- The original C2 denominator is nonzero at the critical center, by the
pinned native C2 factor bound on the line. -/
theorem c2OriginalCameraDenominator_zero_ne_zero :
    c2OriginalCameraDenominator 0 ≠ 0 := by
  have hparam : operatorHeightParameter 0 = nativeLine 0 := by
    simp [operatorHeightParameter, nativeLine]
  rw [c2OriginalCameraDenominator, hparam, factor_two]
  exact c2Factor_nativeLine_ne_zero 0

/-- Critical center belongs to the original scalar domain. -/
theorem c2_operatorHeightParameter_zero_mem_nativeScalarDomain :
    operatorHeightParameter 0 ∈ nativeScalarDomain := by
  norm_num [operatorHeightParameter, nativeScalarDomain]

/-- The head-tail source factorization after the common zero has been
cancelled, at the nonsingular critical center. -/
theorem c2OriginalCompletedCharacteristic_eq_reduced_at_center
    (M : ℕ) :
    completedNativeOperatorCharacteristic 0 =
      c2ReducedCompletionFactor 0 * c2OriginalCompletedBracket M 0 /
        c2ReducedCameraFactor 0 := by
  exact c2OriginalCompletedCharacteristic_eq_reduced_critical_germ_pointwise
    M 0 c2_operatorHeightParameter_zero_mem_nativeScalarDomain
    commonPoleHeightFactor_zero_ne_zero
    c2OriginalCameraDenominator_zero_ne_zero

/-- The original completed source with only the common `s-1` factor removed. -/
def c2ReducedCompletedCharacteristic (M : ℕ) (z : ℂ) : ℂ :=
  c2ReducedCompletionFactor z * c2OriginalCompletedBracket M z /
    c2ReducedCameraFactor z

/-- The identity `F=aB/q` holds as an actual germ at the critical center,
not only as an equality at its center point. -/
theorem c2OriginalCompletedCharacteristic_eq_reduced_eventually
    (M : ℕ) :
    (fun z => completedNativeOperatorCharacteristic z) =ᶠ[nhds (0 : ℂ)]
      (fun z => c2ReducedCompletedCharacteristic M z) := by
  have hs0 : operatorHeightParameter 0 ∈ nativeScalarDomain :=
    c2_operatorHeightParameter_zero_mem_nativeScalarDomain
  have hQ0 : c2OriginalCameraDenominator 0 ≠ 0 :=
    c2OriginalCameraDenominator_zero_ne_zero
  have hX0 : commonPoleHeightFactor 0 ≠ 0 :=
    commonPoleHeightFactor_zero_ne_zero
  have hparamCont : ContinuousAt operatorHeightParameter 0 :=
    operatorHeightParameter_differentiable.differentiableAt.continuousAt
  have hs : ∀ᶠ z in nhds (0 : ℂ), operatorHeightParameter z ∈ nativeScalarDomain :=
    hparamCont.preimage_mem_nhds (isOpen_nativeScalarDomain.mem_nhds hs0)
  have hQcont : ContinuousAt c2OriginalCameraDenominator 0 :=
    c2OriginalCameraDenominator_differentiable.differentiableAt.continuousAt
  have hXcont : ContinuousAt commonPoleHeightFactor 0 :=
    commonPoleHeightFactor_differentiable.differentiableAt.continuousAt
  have hQ : ∀ᶠ z in nhds (0 : ℂ), c2OriginalCameraDenominator z ≠ 0 :=
    hQcont.eventually_ne hQ0
  have hX : ∀ᶠ z in nhds (0 : ℂ), commonPoleHeightFactor z ≠ 0 :=
    hXcont.eventually_ne hX0
  filter_upwards [hs, hQ, hX] with z hsz hQz hXz
  exact c2OriginalCompletedCharacteristic_eq_reduced_critical_germ_pointwise
    M z hsz hXz hQz

/-- A common nonzero differentiable factor cancels from the difference of
half-logarithmic responses. This is the response-level identity used before
extracting any Taylor coefficient. -/
theorem halfLogResponse_commonFactor_cancel
    (X A Q : ℂ → ℂ) (z : ℂ)
    (hX : DifferentiableAt ℂ X z)
    (hA : DifferentiableAt ℂ A z)
    (hQ : DifferentiableAt ℂ Q z)
    (hX0 : X z ≠ 0) (hA0 : A z ≠ 0) (hQ0 : Q z ≠ 0) :
    halfLogResponse A z - halfLogResponse Q z =
      halfLogResponse (fun w => A w / X w) z -
        halfLogResponse (fun w => Q w / X w) z := by
  have hAd : DifferentiableAt ℂ (fun w => A w / X w) z := hA.div hX hX0
  have hQd : DifferentiableAt ℂ (fun w => Q w / X w) z := hQ.div hX hX0
  have hAred0 : A z / X z ≠ 0 := div_ne_zero hA0 hX0
  have hQred0 : Q z / X z ≠ 0 := div_ne_zero hQ0 hX0
  have hAe : (fun w => X w * (A w / X w)) =ᶠ[nhds z] A := by
    filter_upwards [hX.continuousAt.eventually_ne hX0] with w hw
    field_simp [hw]
  have hQe : (fun w => X w * (Q w / X w)) =ᶠ[nhds z] Q := by
    filter_upwards [hX.continuousAt.eventually_ne hX0] with w hw
    field_simp [hw]
  have hAderiv := hAe.deriv_eq
  have hQderiv := hQe.deriv_eq
  have hAval : X z * (A z / X z) = A z := by field_simp [hX0]
  have hQval : X z * (Q z / X z) = Q z := by field_simp [hX0]
  have hAresponse :
      halfLogResponse A z =
        halfLogResponse (fun w => X w * (A w / X w)) z := by
    unfold halfLogResponse
    rw [← hAderiv, ← hAval]
  have hQresponse :
      halfLogResponse Q z =
        halfLogResponse (fun w => X w * (Q w / X w)) z := by
    unfold halfLogResponse
    rw [← hQderiv, ← hQval]
  rw [hAresponse, hQresponse,
    halfLogResponse_mul X (fun w => A w / X w) z hX hAd hX0 hAred0,
    halfLogResponse_mul X (fun w => Q w / X w) z hX hQd hX0 hQred0]
  ring

/-- Original completion-versus-C2-camera log channel. -/
def c2OriginalCompletionCameraLogResponse (z : ℂ) : ℂ :=
  halfLogResponse nativeXiCompletionFactor z -
    halfLogResponse c2OriginalCameraDenominator z

/-- Reduced completion-versus-camera log channel, after cancelling `s-1`. -/
def c2ReducedCompletionCameraLogResponse (z : ℂ) : ℂ :=
  halfLogResponse c2ReducedCompletionFactor z -
    halfLogResponse c2ReducedCameraFactor z

/-- The source-specific response channels agree as germs at the critical
center. All factors and the C2 denominator are their existing definitions. -/
theorem c2CompletionCameraLogResponse_eventuallyEq :
    c2OriginalCompletionCameraLogResponse =ᶠ[nhds (0 : ℂ)]
      c2ReducedCompletionCameraLogResponse := by
  have hstrip0 : (0 : ℂ) ∈ completedNativeHeightDomain :=
    zero_mem_completedNativeHeightDomain
  have hstrip : ∀ᶠ z in nhds (0 : ℂ), z ∈ completedNativeHeightDomain :=
    isOpen_completedNativeHeightDomain.mem_nhds hstrip0
  have hA0 : nativeXiCompletionFactor 0 ≠ 0 :=
    nativeXiCompletionFactor_ne_zero hstrip0
  have hQ0 : c2OriginalCameraDenominator 0 ≠ 0 :=
    c2OriginalCameraDenominator_zero_ne_zero
  have hX0 : commonPoleHeightFactor 0 ≠ 0 :=
    commonPoleHeightFactor_zero_ne_zero
  have hAcont : ContinuousAt nativeXiCompletionFactor 0 :=
    (nativeXiCompletionFactor_differentiableAt hstrip0).continuousAt
  have hQall : Differentiable ℂ c2OriginalCameraDenominator :=
    c2OriginalCameraDenominator_differentiable
  have hXall : Differentiable ℂ commonPoleHeightFactor :=
    commonPoleHeightFactor_differentiable
  have hQcont : ContinuousAt c2OriginalCameraDenominator 0 :=
    (hQall.differentiableAt).continuousAt
  have hXcont : ContinuousAt commonPoleHeightFactor 0 :=
    (hXall.differentiableAt).continuousAt
  have hAne : ∀ᶠ z in nhds (0 : ℂ), nativeXiCompletionFactor z ≠ 0 :=
    hAcont.eventually_ne hA0
  have hQne : ∀ᶠ z in nhds (0 : ℂ), c2OriginalCameraDenominator z ≠ 0 :=
    hQcont.eventually_ne hQ0
  have hXne : ∀ᶠ z in nhds (0 : ℂ), commonPoleHeightFactor z ≠ 0 :=
    hXcont.eventually_ne hX0
  filter_upwards [hstrip, hAne, hQne, hXne] with z hz hAz hQz hXz
  have hAd : DifferentiableAt ℂ nativeXiCompletionFactor z :=
    nativeXiCompletionFactor_differentiableAt (by
      change operatorHeightParameter z ∈ genuineCriticalStrip at hz
      exact hz)
  exact halfLogResponse_commonFactor_cancel commonPoleHeightFactor
    nativeXiCompletionFactor c2OriginalCameraDenominator z
    (hXall.differentiableAt) hAd (hQall.differentiableAt)
    hXz hAz hQz

/-- Coefficient of the `n`th centered Taylor jet of a response germ. -/
def c2ResponseTaylorJet (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- Every Taylor jet of the original completion/camera channels equals the
jet after exact common-pole cancellation. -/
theorem c2CompletionCameraLogResponse_taylorJet_eq (n : ℕ) :
    c2ResponseTaylorJet c2OriginalCompletionCameraLogResponse n =
      c2ResponseTaylorJet c2ReducedCompletionCameraLogResponse n := by
  unfold c2ResponseTaylorJet
  rw [c2CompletionCameraLogResponse_eventuallyEq.iteratedDeriv_eq n]

/-- Existing source normalization: `-F'/F` is twice the half-log response,
and the existing odd boundary coefficient is twice the prime-depth response.
This preserves the repository's canonical `h_j` convention. -/
theorem c2NativeOddBoundaryCoefficient_eq_twiceCanonicalResponse (j : ℕ) :
    nativeSourceOddBoundaryCoefficient j = 2 * primeDepthGeometricMoment j :=
  nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment j

end

end CarrySelfAdjointOperator

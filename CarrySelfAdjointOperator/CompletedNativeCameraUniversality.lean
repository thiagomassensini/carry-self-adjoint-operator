import CarrySelfAdjointOperator.CompletedNativeAllOrderCameraBridge
import CarrySelfAdjointOperator.GenuineMomentOperatorUniqueness

/-!
# Exact multibase universality of completed camera moments

Normalize each head-plus-exact-tail camera by its nonvanishing camera factor.
The resulting real-axis function equals the common completed characteristic.
Its derivatives, even Taylor coefficients, recursively constructed logarithmic
moments, and both Hankel towers therefore agree in every supported base and
at every cutoff.

Canonical Jacobi and finite height operators inherit this equality under
their existing positivity hypotheses. The cutoff independence here concerns
the exact head-plus-tail characteristic.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Exact completed camera with its camera factor removed and its common
completion factor retained. -/
def normalizedCompletedNativeCameraCharacteristic
    (camera cutoff : ℕ) (time : ℝ) : ℂ :=
  nativeXiCompletionFactor (time : ℂ) *
      completedNativeCharacteristic camera cutoff (nativeLine time) /
    factor camera (nativeLine time)

/-- Every supported normalized camera is the same function on the entire
real height axis. Camera-factor nonvanishing is discharged internally. -/
theorem normalizedCompletedNativeCameraCharacteristic_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    normalizedCompletedNativeCameraCharacteristic camera cutoff =
      fun time : ℝ ↦
        completedNativeOperatorCharacteristic (time : ℂ) := by
  funext time
  unfold normalizedCompletedNativeCameraCharacteristic
  apply (div_eq_iff (factor_nativeLine_ne_zero hcamera time)).2
  exact
    (nativeXiCompletionFactor_mul_completedNativeCharacteristic_nativeLine
      hcamera cutoff time).trans (mul_comm _ _)

/-- Real derivatives of a normalized completed camera are exactly the
complex derivatives of the common characteristic, in every order. -/
theorem iteratedDeriv_normalizedCompletedNativeCameraCharacteristic
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff order : ℕ) (time : ℝ) :
    iteratedDeriv order
        (normalizedCompletedNativeCameraCharacteristic camera cutoff) time =
      iteratedDeriv order completedNativeOperatorCharacteristic
        (time : ℂ) := by
  rw [normalizedCompletedNativeCameraCharacteristic_eq hcamera cutoff]
  exact iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal
    order time

/-- Even Taylor coefficient read directly from the normalized camera. -/
def completedNativeCameraEvenCoefficient
    (camera cutoff n : ℕ) : ℂ :=
  ((Nat.factorial (2 * n) : ℂ)⁻¹) •
    iteratedDeriv (2 * n)
      (normalizedCompletedNativeCameraCharacteristic camera cutoff) 0

/-- The camera coefficient agrees with the common complex Taylor
coefficient before taking its real part. -/
theorem completedNativeCameraEvenCoefficient_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff n : ℕ) :
    completedNativeCameraEvenCoefficient camera cutoff n =
      completedNativeEvenCharacteristicCoefficient n := by
  unfold completedNativeCameraEvenCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  rw [iteratedDeriv_normalizedCompletedNativeCameraCharacteristic hcamera]

/-- Real coefficients used by the camera's logarithmic moment recurrence. -/
def completedNativeCameraRealEvenCoefficient
    (camera cutoff n : ℕ) : ℝ :=
  (completedNativeCameraEvenCoefficient camera cutoff n).re

theorem completedNativeCameraRealEvenCoefficient_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff n : ℕ) :
    completedNativeCameraRealEvenCoefficient camera cutoff n =
      completedNativeRealEvenCharacteristicCoefficient n := by
  unfold completedNativeCameraRealEvenCoefficient
    completedNativeRealEvenCharacteristicCoefficient
  rw [completedNativeCameraEvenCoefficient_eq hcamera]

/-- The recurrence's denominator is nonzero in every supported camera. -/
theorem completedNativeCameraRealEvenCoefficient_zero_ne_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    completedNativeCameraRealEvenCoefficient camera cutoff 0 ≠ 0 := by
  rw [completedNativeCameraRealEvenCoefficient_eq hcamera]
  exact completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero

/-- Root-free logarithmic moments constructed from the camera coefficients
themselves, using the same causal recurrence as the common characteristic. -/
def completedNativeCameraLogDerivativeMoment
    (camera cutoff : ℕ) : ℕ → ℝ :=
  Nat.lt_wfRel.wf.fix fun n previous =>
    (-((n + 1 : ℕ) : ℝ) *
        completedNativeCameraRealEvenCoefficient camera cutoff (n + 1) -
      ∑ k : Fin n,
        previous k k.isLt *
          completedNativeCameraRealEvenCoefficient camera cutoff (n - k)) /
      completedNativeCameraRealEvenCoefficient camera cutoff 0

/-- Constructing the moments in any supported camera gives exactly the
canonical completed-native moment sequence. -/
theorem completedNativeCameraLogDerivativeMoment_eq_canonical
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    completedNativeCameraLogDerivativeMoment camera cutoff =
      canonicalCompletedNativeLogDerivativeMoment := by
  unfold completedNativeCameraLogDerivativeMoment
    canonicalCompletedNativeLogDerivativeMoment
  simp_rw [completedNativeCameraRealEvenCoefficient_eq hcamera]

/-- The camera construction satisfies its own division-free coefficient
identity. -/
theorem completedNativeCameraLogDerivativeMoment_camera_recurrence
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    IsLogDerivativeMomentSequence
      (completedNativeCameraRealEvenCoefficient camera cutoff)
      (completedNativeCameraLogDerivativeMoment camera cutoff) := by
  intro n
  simpa only [completedNativeCameraRealEvenCoefficient_eq hcamera,
    completedNativeCameraLogDerivativeMoment_eq_canonical hcamera,
    neg_mul] using
      canonicalCompletedNativeLogDerivativeMoment_real_recurrence n

/-- The concrete camera moments satisfy the completed-native moment
interface used by the operator construction. -/
theorem completedNativeCameraLogDerivativeMoment_isMomentSequence
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    IsCompletedNativeLogDerivativeMomentSequence
      (completedNativeCameraLogDerivativeMoment camera cutoff) := by
  rw [completedNativeCameraLogDerivativeMoment_eq_canonical hcamera]
  exact canonicalCompletedNativeLogDerivativeMoment_isMomentSequence

/-- Each normalized camera has one and only one real logarithmic moment
sequence, with an explicit recursive witness. -/
theorem existsUnique_completedNativeCameraLogDerivativeMoment
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    ∃! moments : ℕ → ℝ,
      IsLogDerivativeMomentSequence
        (completedNativeCameraRealEvenCoefficient camera cutoff) moments := by
  refine ⟨completedNativeCameraLogDerivativeMoment camera cutoff,
    completedNativeCameraLogDerivativeMoment_camera_recurrence
      hcamera cutoff, ?_⟩
  intro moments hrel
  exact hrel.unique
    (completedNativeCameraRealEvenCoefficient_zero_ne_zero hcamera cutoff)
    (completedNativeCameraLogDerivativeMoment_camera_recurrence
      hcamera cutoff)

/-- The camera recurrence and the common completed-native moment interface
specify exactly the same real sequences. -/
theorem completedNativeCamera_momentSequence_iff
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff : ℕ) (moments : ℕ → ℝ) :
    IsLogDerivativeMomentSequence
        (completedNativeCameraRealEvenCoefficient camera cutoff) moments ↔
      IsCompletedNativeLogDerivativeMomentSequence moments := by
  constructor
  · intro hrel
    have heq := hrel.unique
      (completedNativeCameraRealEvenCoefficient_zero_ne_zero hcamera cutoff)
      (completedNativeCameraLogDerivativeMoment_camera_recurrence
        hcamera cutoff)
    rw [heq]
    exact completedNativeCameraLogDerivativeMoment_isMomentSequence
      hcamera cutoff
  · intro hrel
    rw [completedNativeLogDerivativeMoment_eq_canonical hrel,
      ← completedNativeCameraLogDerivativeMoment_eq_canonical hcamera cutoff]
    exact completedNativeCameraLogDerivativeMoment_camera_recurrence
      hcamera cutoff

/-- Unconditional multibase synthesis: all normalized jets, all recursively
constructed moments, and both finite Hankel towers agree exactly. -/
theorem completedNativeCameraUniversality
    {camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂)
    (cutoff₁ cutoff₂ : ℕ) :
    (∀ (order : ℕ) (time : ℝ),
      iteratedDeriv order
          (normalizedCompletedNativeCameraCharacteristic camera₁ cutoff₁)
          time =
        iteratedDeriv order
          (normalizedCompletedNativeCameraCharacteristic camera₂ cutoff₂)
          time) ∧
    completedNativeCameraLogDerivativeMoment camera₁ cutoff₁ =
      completedNativeCameraLogDerivativeMoment camera₂ cutoff₂ ∧
    (∀ N : ℕ,
      hankelGram (completedNativeCameraLogDerivativeMoment camera₁ cutoff₁) N =
          hankelGram (completedNativeCameraLogDerivativeMoment camera₂ cutoff₂) N ∧
      shiftedHankel (completedNativeCameraLogDerivativeMoment camera₁ cutoff₁) N =
        shiftedHankel (completedNativeCameraLogDerivativeMoment camera₂ cutoff₂) N) := by
  have hmoments :
      completedNativeCameraLogDerivativeMoment camera₁ cutoff₁ =
        completedNativeCameraLogDerivativeMoment camera₂ cutoff₂ :=
    (completedNativeCameraLogDerivativeMoment_eq_canonical
      hcamera₁ cutoff₁).trans
      (completedNativeCameraLogDerivativeMoment_eq_canonical
        hcamera₂ cutoff₂).symm
  refine ⟨?_, hmoments, ?_⟩
  · intro order time
    rw [iteratedDeriv_normalizedCompletedNativeCameraCharacteristic hcamera₁,
      iteratedDeriv_normalizedCompletedNativeCameraCharacteristic hcamera₂]
  · intro N
    constructor <;> rw [hmoments]

/-- Canonical finite Jacobi sections are independent of camera and cutoff
under their existing finite Gram positivity hypotheses. -/
theorem completedNativeCamera_finiteJacobi_independent
    {camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂)
    (cutoff₁ cutoff₂ N : ℕ)
    (hgram₁ :
      (hankelGram (completedNativeCameraLogDerivativeMoment camera₁ cutoff₁) N).PosDef)
    (hgram₂ :
      (hankelGram (completedNativeCameraLogDerivativeMoment camera₂ cutoff₂) N).PosDef) :
    canonicalFiniteJacobiSection
        (completedNativeCameraLogDerivativeMoment camera₁ cutoff₁) N hgram₁ =
      canonicalFiniteJacobiSection
        (completedNativeCameraLogDerivativeMoment camera₂ cutoff₂) N hgram₂ := by
  exact canonicalFiniteJacobiSection_eq_of_completedNativeLogDerivativeMoments
    (completedNativeCameraLogDerivativeMoment_isMomentSequence hcamera₁ cutoff₁)
    (completedNativeCameraLogDerivativeMoment_isMomentSequence hcamera₂ cutoff₂)
    N hgram₁ hgram₂

/-- The infinite coefficient matrix selected by the canonical principal
tower is independent of camera under all-order Gram positivity. -/
theorem completedNativeCamera_jacobiTower_independent
    {camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂)
    (cutoff₁ cutoff₂ : ℕ)
    (hgram₁ : ∀ N : ℕ,
      (hankelGram (completedNativeCameraLogDerivativeMoment camera₁ cutoff₁) N).PosDef)
    (hgram₂ : ∀ N : ℕ,
      (hankelGram (completedNativeCameraLogDerivativeMoment camera₂ cutoff₂) N).PosDef) :
    canonicalJacobiTowerLimitMatrix
        (completedNativeCameraLogDerivativeMoment camera₁ cutoff₁) hgram₁ =
      canonicalJacobiTowerLimitMatrix
        (completedNativeCameraLogDerivativeMoment camera₂ cutoff₂) hgram₂ := by
  exact canonicalJacobiTowerLimitMatrix_eq_of_completedNativeLogDerivativeMoments
    (completedNativeCameraLogDerivativeMoment_isMomentSequence hcamera₁ cutoff₁)
    (completedNativeCameraLogDerivativeMoment_isMomentSequence hcamera₂ cutoff₂)
    hgram₁ hgram₂

private theorem finiteHeightOperator_eq_of_matrix_eq
    {N : ℕ} {jacobi₁ jacobi₂ : Matrix (Fin N) (Fin N) ℝ}
    (heq : jacobi₁ = jacobi₂)
    (hjacobi₁ : jacobi₁.PosDef) (hjacobi₂ : jacobi₂.PosDef) :
    finiteHeightOperator hjacobi₁ = finiteHeightOperator hjacobi₂ := by
  subst jacobi₂
  rfl

/-- The positive finite height matrices obtained by `J_N^(-1/2)` also agree
between cameras whenever their Jacobi sections are positive definite. -/
theorem completedNativeCamera_finiteHeight_independent
    {camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂)
    (cutoff₁ cutoff₂ N : ℕ)
    (hgram₁ :
      (hankelGram (completedNativeCameraLogDerivativeMoment camera₁ cutoff₁) N).PosDef)
    (hgram₂ :
      (hankelGram (completedNativeCameraLogDerivativeMoment camera₂ cutoff₂) N).PosDef)
    (hjacobi₁ :
      (canonicalFiniteJacobiSection
        (completedNativeCameraLogDerivativeMoment camera₁ cutoff₁) N hgram₁).PosDef)
    (hjacobi₂ :
      (canonicalFiniteJacobiSection
        (completedNativeCameraLogDerivativeMoment camera₂ cutoff₂) N hgram₂).PosDef) :
    finiteHeightOperator hjacobi₁ = finiteHeightOperator hjacobi₂ := by
  exact finiteHeightOperator_eq_of_matrix_eq
    (completedNativeCamera_finiteJacobi_independent
      hcamera₁ hcamera₂ cutoff₁ cutoff₂ N hgram₁ hgram₂)
    hjacobi₁ hjacobi₂

end

end CarrySelfAdjointOperator

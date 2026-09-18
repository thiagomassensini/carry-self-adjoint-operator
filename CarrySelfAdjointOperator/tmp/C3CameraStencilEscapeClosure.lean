import C3ProjectiveHilbertRBBridge
import ExactCutoffCameraGram
import NativeCarrySpectralWeyl.Infinite.CameraCompletion

/-!
# Literal camera stencils: exact Gram mass and escape from the native Hilbert space

This file decides whether the cutoff-normalized literal camera stencil has a
strong limit in the native vertical Hilbert carrier.  The two relevant facts
are kept together:

* every fixed depth coefficient tends to zero after the canonical
  `cutoff^(-1/2)` normalization;
* the exact cutoff Gram identity makes the squared norm tend to the strictly
  positive intrinsic all-bases Gram diagonal.

Consequently the normalized stencil has no strong limit in `CarryVerticalL2`.
The limiting camera vector therefore belongs to the intrinsic camera
completion (or, for raw state evaluation, to a rigged/dual boundary port),
not to the native depth Hilbert space as an ordinary vector.
-/

open scoped BigOperators Topology lp ENNReal NNReal
open Filter

noncomputable section

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Limits
open NativeCarrySpectralWeyl.Infinite

/-- The complete finite literal camera row, embedded in the native complex
depth Hilbert space. -/
def literalFiniteCameraStencil (cutoff camera : ℕ) : CarryVerticalL2 :=
  ∑ n ∈ Finset.range (finiteCameraWindow camera cutoff),
    (lp.single 2 n (finiteCoefficientAt camera cutoff n : ℂ) :
      CarryVerticalL2)

/-- Canonical covariance normalization.  Its square is exactly `cutoff⁻¹`. -/
def cutoffGramNormalization (cutoff : ℕ) : ℝ :=
  √((cutoff : ℝ)⁻¹)

/-- The cutoff-normalized literal camera row. -/
def normalizedLiteralFiniteCameraStencil
    (cutoff camera : ℕ) : CarryVerticalL2 :=
  (cutoffGramNormalization cutoff : ℂ) •
    literalFiniteCameraStencil cutoff camera

@[simp] theorem cutoffGramNormalization_sq (cutoff : ℕ) :
    cutoffGramNormalization cutoff ^ 2 = (cutoff : ℝ)⁻¹ := by
  rw [cutoffGramNormalization, Real.sq_sqrt]
  positivity

theorem tendsto_cutoffGramNormalization_zero :
    Tendsto cutoffGramNormalization atTop (nhds 0) := by
  change Tendsto (fun cutoff : ℕ ↦ √((cutoff : ℝ)⁻¹)) atTop (nhds 0)
  simpa only [Real.sqrt_zero] using
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt

/-- The finite Hilbert vector has exactly the literal finite Gram as its
squared norm. -/
theorem norm_sq_literalFiniteCameraStencil
    (camera cutoff : ℕ) :
    ‖literalFiniteCameraStencil cutoff camera‖ ^ 2 =
      literalFiniteCameraGram cutoff camera camera := by
  rw [literalFiniteCameraStencil]
  have hnorm := lp.norm_sum_single
    (p := (2 : ℝ≥0∞)) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (fun n : ℕ ↦ (finiteCoefficientAt camera cutoff n : ℂ))
    (Finset.range (finiteCameraWindow camera cutoff))
  norm_num only [ENNReal.toReal_ofNat] at hnorm
  rw [Real.rpow_two] at hnorm
  calc
    ‖∑ n ∈ Finset.range (finiteCameraWindow camera cutoff),
        (lp.single 2 n (finiteCoefficientAt camera cutoff n : ℂ) :
          CarryVerticalL2)‖ ^ 2 =
        ∑ n ∈ Finset.range (finiteCameraWindow camera cutoff),
          ‖(finiteCoefficientAt camera cutoff n : ℂ)‖ ^ 2 := hnorm
    _ = literalFiniteCameraGram cutoff camera camera := by
      rw [literalFiniteCameraGram]
      simp only [pairFiniteWindow, min_self]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]
      simpa only [pow_two] using
        (sq_abs (finiteCoefficientAt camera cutoff n))

/-- Exact finite identity for the squared norm after covariance
normalization. -/
theorem norm_sq_normalizedLiteralFiniteCameraStencil
    (camera cutoff : ℕ) :
    ‖normalizedLiteralFiniteCameraStencil cutoff camera‖ ^ 2 =
      (cutoff : ℝ)⁻¹ * literalFiniteCameraGram cutoff camera camera := by
  calc
    ‖normalizedLiteralFiniteCameraStencil cutoff camera‖ ^ 2 =
        ‖(cutoffGramNormalization cutoff : ℂ)‖ ^ 2 *
          ‖literalFiniteCameraStencil cutoff camera‖ ^ 2 := by
      rw [normalizedLiteralFiniteCameraStencil, norm_smul]
      ring
    _ = (cutoff : ℝ)⁻¹ *
        literalFiniteCameraGram cutoff camera camera := by
      have hnormalization : 0 ≤ cutoffGramNormalization cutoff :=
        Real.sqrt_nonneg _
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnormalization, cutoffGramNormalization_sq,
        norm_sq_literalFiniteCameraStencil]

/-- Pointwise formula for the literal finite stencil at every depth,
including the zero extension beyond its emitted window. -/
@[simp] theorem literalFiniteCameraStencil_apply
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff n : ℕ) :
    literalFiniteCameraStencil cutoff camera n =
      (finiteCoefficientAt camera cutoff n : ℂ) := by
  rw [literalFiniteCameraStencil]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
    Finset.sum_pi_single]
  by_cases hn : n < finiteCameraWindow camera cutoff
  · simp [hn]
  · have hout : finiteCameraWindow camera cutoff ≤ n := Nat.le_of_not_gt hn
    rw [finiteCoefficientAt_eq_zero_of_window_le hcamera hout]
    simp [hn]

@[simp] theorem normalizedLiteralFiniteCameraStencil_apply
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff n : ℕ) :
    normalizedLiteralFiniteCameraStencil cutoff camera n =
      (cutoffGramNormalization cutoff : ℂ) *
        finiteCoefficientAt camera cutoff n := by
  change (cutoffGramNormalization cutoff : ℂ) *
      literalFiniteCameraStencil cutoff camera n = _
  rw [literalFiniteCameraStencil_apply hcamera]

/-- At every fixed native depth, the normalized camera stencil vanishes.
This is the coefficientwise half of the escape-of-mass statement. -/
theorem tendsto_normalizedLiteralFiniteCameraStencil_apply_zero
    (camera : ℕ) (hcamera : 2 ≤ camera) (n : ℕ) :
    Tendsto
      (fun cutoff : ℕ ↦ normalizedLiteralFiniteCameraStencil cutoff camera n)
      atTop (nhds 0) := by
  have hnormalizationReal := tendsto_cutoffGramNormalization_zero
  have hnormalization : Tendsto
      (fun cutoff : ℕ ↦ (cutoffGramNormalization cutoff : ℂ))
      atTop (nhds 0) := by
    change Tendsto (Complex.ofReal ∘ cutoffGramNormalization)
      atTop (nhds (Complex.ofReal 0))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      hnormalizationReal
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun cutoff : ℕ ↦
        (finiteCoefficientAt camera cutoff n : ℂ)) := by
    change ∃ bound : ℝ, ∀ᶠ cutoff : ℕ in atTop,
      ‖(finiteCoefficientAt camera cutoff n : ℂ)‖ ≤ bound
    refine ⟨(camera + 4 : ℕ), Filter.Eventually.of_forall fun cutoff ↦ ?_⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_ofNat] using
      (abs_finiteCoefficientAt_le (cutoff := cutoff) (n := n) hcamera)
  have hzero := hnormalization.zero_smul_isBoundedUnder_le hbounded
  simpa only [normalizedLiteralFiniteCameraStencil_apply hcamera,
    smul_eq_mul, Function.comp_apply] using hzero

/-- The normalized squared norm tends to the intrinsic all-bases Gram
diagonal attached to this camera. -/
theorem tendsto_norm_sq_normalizedLiteralFiniteCameraStencil
    (camera : CameraIndex) :
    Tendsto
      (fun cutoff : ℕ ↦
        ‖normalizedLiteralFiniteCameraStencil cutoff (cameraLabel camera)‖ ^ 2)
      atTop (nhds (gramKernel camera camera)) := by
  let family : Unit → ℕ := fun _ ↦ cameraLabel camera
  have hperiod : 0 < pairPeriod camera camera := pairPeriod_pos camera camera
  have hcamera : ∀ i : Unit, 2 ≤ family i := fun _ ↦ camera.property
  have hcommon : IsCommonProfilePeriod (pairPeriod camera camera) family := by
    intro i
    exact cameraSlope_dvd_pairPeriod_left camera camera
  have hgram := tendsto_normalizedLiteralFiniteCameraGram_apply
    (period := pairPeriod camera camera) (camera := family)
    hperiod hcamera hcommon () ()
  have hnorm :
      (fun cutoff : ℕ ↦
        ‖normalizedLiteralFiniteCameraStencil cutoff (cameraLabel camera)‖ ^ 2) =ᶠ[atTop]
      (fun cutoff : ℕ ↦ (cutoff : ℝ)⁻¹ *
        literalFiniteCameraGram cutoff (cameraLabel camera)
          (cameraLabel camera)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ h ↦ h⟩] with cutoff hcutoff
    exact norm_sq_normalizedLiteralFiniteCameraStencil _ _
  have hgram' : Tendsto
      (fun cutoff : ℕ ↦
        (cutoff : ℝ)⁻¹ *
          literalFiniteCameraGram cutoff (cameraLabel camera)
            (cameraLabel camera))
      atTop (nhds (gramKernel camera camera)) := by
    simpa only [family, periodicGramMatrix_apply, gramKernel,
      periodicMeanKernel] using hgram
  exact hgram'.congr' hnorm.symm

/-- Every all-bases camera carries strictly positive limiting Gram mass. -/
theorem gramKernel_self_pos (camera : CameraIndex) :
    0 < gramKernel camera camera := by
  have hsingle : Finsupp.single camera (1 : ℝ) ≠ 0 :=
    Finsupp.single_ne_zero.mpr one_ne_zero
  have hpos := gramForm_pos hsingle
  simpa using hpos

/-- Pairwise all-bases closure: the normalized literal finite stencil Gram
converges to the inner product of the two canonical vectors in the intrinsic
camera Hilbert completion. -/
theorem tendsto_normalizedLiteralFiniteCameraGram_cameraVector
    (camera₁ camera₂ : CameraIndex) :
    Tendsto
      (fun cutoff : ℕ ↦ (cutoff : ℝ)⁻¹ *
        literalFiniteCameraGram cutoff (cameraLabel camera₁)
          (cameraLabel camera₂))
      atTop
      (nhds (inner ℝ (cameraVector camera₁) (cameraVector camera₂))) := by
  let family : Fin 2 → ℕ :=
    ![cameraLabel camera₁, cameraLabel camera₂]
  have hcamera : ∀ i : Fin 2, 2 ≤ family i := by
    intro i
    fin_cases i
    · exact camera₁.property
    · exact camera₂.property
  have hcommon : IsCommonProfilePeriod (pairPeriod camera₁ camera₂) family := by
    intro i
    fin_cases i
    · exact cameraSlope_dvd_pairPeriod_left camera₁ camera₂
    · exact cameraSlope_dvd_pairPeriod_right camera₁ camera₂
  have hgram := tendsto_normalizedLiteralFiniteCameraGram_apply
    (period := pairPeriod camera₁ camera₂) (camera := family)
    (pairPeriod_pos camera₁ camera₂) hcamera hcommon 0 1
  simpa only [family, Matrix.cons_val_zero, Matrix.cons_val_one,
    periodicGramMatrix_apply, gramKernel, periodicMeanKernel,
    inner_cameraVector] using hgram

/-- Diagonal spelling of the closure theorem: the mass retained by the
escaping depth stencil is exactly the squared norm of the canonical vector
in `CameraHilbert`. -/
theorem tendsto_norm_sq_normalizedLiteralFiniteCameraStencil_cameraHilbert
    (camera : CameraIndex) :
    Tendsto
      (fun cutoff : ℕ ↦
        ‖normalizedLiteralFiniteCameraStencil cutoff (cameraLabel camera)‖ ^ 2)
      atTop (nhds (‖cameraVector camera‖ ^ 2)) := by
  rw [norm_cameraVector_sq]
  exact tendsto_norm_sq_normalizedLiteralFiniteCameraStencil camera

/-- **Strong-limit obstruction.**  The normalized literal camera stencil
cannot converge strongly in the native depth Hilbert space.  Any hypothetical
strong limit has every coordinate zero, while the exact Gram identity forces
its norm to retain positive mass. -/
theorem not_exists_strong_limit_normalizedLiteralFiniteCameraStencil
    (camera : CameraIndex) :
    ¬ ∃ x : CarryVerticalL2,
      Tendsto
        (fun cutoff : ℕ ↦
          normalizedLiteralFiniteCameraStencil cutoff (cameraLabel camera))
        atTop (nhds x) := by
  rintro ⟨x, hx⟩
  have hxzero : x = 0 := by
    ext n
    have heval : Tendsto
        (fun cutoff : ℕ ↦
          normalizedLiteralFiniteCameraStencil cutoff
            (cameraLabel camera) n)
        atTop (nhds (x n)) := by
      exact ((lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 2 n).continuous.tendsto x).comp hx
    have hcoordinate :=
      tendsto_normalizedLiteralFiniteCameraStencil_apply_zero
        (cameraLabel camera) camera.property n
    exact tendsto_nhds_unique heval hcoordinate
  subst x
  have hnormZero : Tendsto
      (fun cutoff : ℕ ↦
        ‖normalizedLiteralFiniteCameraStencil cutoff (cameraLabel camera)‖ ^ 2)
      atTop (nhds 0) := by
    simpa using hx.norm.pow 2
  have hnormGram :=
    tendsto_norm_sq_normalizedLiteralFiniteCameraStencil camera
  have hzero : gramKernel camera camera = 0 :=
    tendsto_nhds_unique hnormGram hnormZero
  exact (ne_of_gt (gramKernel_self_pos camera)) hzero

end NativeCarryC3Crosswalk

#print axioms NativeCarryC3Crosswalk.norm_sq_normalizedLiteralFiniteCameraStencil
#print axioms NativeCarryC3Crosswalk.tendsto_normalizedLiteralFiniteCameraStencil_apply_zero
#print axioms NativeCarryC3Crosswalk.tendsto_norm_sq_normalizedLiteralFiniteCameraStencil
#print axioms NativeCarryC3Crosswalk.tendsto_normalizedLiteralFiniteCameraGram_cameraVector
#print axioms NativeCarryC3Crosswalk.not_exists_strong_limit_normalizedLiteralFiniteCameraStencil

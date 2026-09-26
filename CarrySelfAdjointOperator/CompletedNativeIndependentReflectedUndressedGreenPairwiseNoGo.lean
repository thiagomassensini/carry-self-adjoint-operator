import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedUndressedGreenGerm
import Mathlib.Tactic

/-!
# Pairwise no-go for the diagonal undressed Green port

The undressed port currently duplicates its ordinary source in both Green
legs.  Since the Green form is alternating between those legs, this forces
every undressed camera-pair kernel to vanish by definition.  This is a
structural diagnosis of the present carrier, not an analytic continuation of
the sewn germ theorem.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section
set_option autoImplicit false

/-! ## Diagonal ports are Green-isotropic -/

/-- Any two ports produced by the current undressed extractor have zero Green
pairing: each port duplicates its ordinary source in the two Green legs. -/
theorem greenForm_undressedGreenPort_eq_zero
    (N : ℕ) (direct reflected : CanonicalCompletedC3HilbertState) :
    greenForm (𝕜 := ℂ) (undressedGreenPort N direct)
      (undressedGreenPort N reflected) = 0 := by
  simp [undressedGreenPort, greenForm]

/-- Consequently every camera-pair undressed Green kernel is pointwise zero.
This follows directly from the two-leg port definition and does not use the
analytic germ theorem for the sewn total. -/
theorem canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_eq_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
      M q hq0 hq1 S u v directCamera reflectedCamera = 0 := by
  unfold canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
    cameraResolvedIndependentReflectedUndressedDirectGreenPort
    cameraResolvedIndependentReflectedUndressedReflectedGreenPort
  apply greenForm_undressedGreenPort_eq_zero

/-! ## The requested witnesses cannot exist -/

/-- There is no central nonzero camera-pair witness in the current undressed
carrier, even before restricting to the material finite atlas. -/
theorem canonicalC3IndependentReflectedUndressedGreen_no_center_pairwise_witness
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ¬ ∃ directCamera reflectedCamera : ℕ,
        canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
          M q hq0 hq1 S 0 0 directCamera reflectedCamera ≠ 0 := by
  rintro ⟨directCamera, reflectedCamera, hnonzero⟩
  exact hnonzero
    (canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_eq_zero
      M q hq0 hq1 S 0 0 directCamera reflectedCamera)

/-- In particular, no nonzero central witness exists inside the finite camera
atlas.  The atlas membership assumptions are retained in the statement to
match the intended sewn-cancellation witness precisely. -/
theorem canonicalC3IndependentReflectedUndressedGreen_no_center_atlas_witness
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ¬ ∃ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∃ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
            M q hq0 hq1 S 0 0 directCamera reflectedCamera ≠ 0 := by
  rintro ⟨directCamera, _, reflectedCamera, _, hnonzero⟩
  exact hnonzero
    (canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_eq_zero
      M q hq0 hq1 S 0 0 directCamera reflectedCamera)

/-- The same structural obstruction rules out the proposed local alternative:
there is no pointwise nonzero undressed camera-pair kernel at any reflected
coordinate.  This is not a globalization of the sewn analytic germ; it is a
direct consequence of the diagonal two-leg extractor. -/
theorem canonicalC3IndependentReflectedUndressedGreen_no_pairwise_witness
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ¬ ∃ (u v : ℂ) (directCamera reflectedCamera : ℕ),
        canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
          M q hq0 hq1 S u v directCamera reflectedCamera ≠ 0 := by
  rintro ⟨u, v, directCamera, reflectedCamera, hnonzero⟩
  exact hnonzero
    (canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_eq_zero
      M q hq0 hq1 S u v directCamera reflectedCamera)

end

end CarrySelfAdjointOperator

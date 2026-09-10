import CarrySelfAdjointOperator.EnrichedMovingCameraCompletedNaimarkCrosswalk
import CarrySelfAdjointOperator.CompletedC3NaimarkCoisometricBlock
import CarrySelfAdjointOperator.FiniteEnrichedCameraState
import NativeCarrySpectralWeyl.Infinite.CameraCompletion
import NativeCarrySpectralWeyl.Infinite.Naimark
import Mathlib.Tactic

/-!
# Finite enriched camera / completed Naimark escape intertwining

The finite canonical camera projection acts on the state side of a finite
matrix, whereas the completed Naimark projection acts on the realified
ambient Naimark space.  The existing API does not supply an embedding between
those two domains.  This file therefore does two things only:

* records the exact factorisations of the finite and completed projectors;
* proves the algebraic reduction from the two missing intertwining squares
  (readout and synthesis) to projector and escape intertwining.

No finite-to-completed embedding, cutoff identification, or blind-sector
identification is asserted here.  The predicate
NaimarkProjectorIntertwiningSeam is the smallest typed interface that a
future geometric crosswalk must instantiate.
-/

open scoped BigOperators Matrix lp

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite

namespace CarrySelfAdjointOperator

noncomputable section

/-! ## Exact finite and completed projector factorisations -/

/-- The finite state-side projection is exactly synthesis after readout. -/
theorem finiteCanonicalCameraProjection_factorization
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ) :
    finiteCanonicalCameraProjection C =
      finiteCanonicalCameraSynthesis C * finiteCanonicalCameraReadout C := by
  rfl

/-- The finite blind projection is exactly the state identity minus the
coherent camera projection. -/
theorem finiteCanonicalCameraBlindProjection_factorization
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ) :
    finiteCanonicalCameraBlindProjection C =
      (1 : Matrix state state ℝ) - finiteCanonicalCameraProjection C := by
  rfl

/-- The finite projection factorisation lifted to Hilbert-valued finite
families.  The external matrix acts only on the family index. -/
theorem finiteCanonicalCameraProjection_hilbert_action
    {camera state H : Type*}
    [Fintype camera] [Fintype state]
    [NormedAddCommGroup H] [Module ℂ H]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X : FiniteHilbertFamily state H) :
    finiteHilbertMatrixSynthesis
        (finiteCanonicalCameraProjection C) X =
      finiteCanonicalCameraHilbertSynthesis C
        (finiteCanonicalCameraHilbertReadout C X) := by
  change finiteHilbertMatrixSynthesis
      (finiteCanonicalCameraSynthesis C * finiteCanonicalCameraReadout C) X =
    finiteHilbertMatrixSynthesis (finiteCanonicalCameraSynthesis C)
      (finiteHilbertMatrixSynthesis (finiteCanonicalCameraReadout C) X)
  rw [finiteHilbertMatrixSynthesis_comp]

/-- The completed ambient projection is the Naimark port followed by its
realified adjoint. -/
theorem canonicalCompletedC3AmbientPortProjection_factorization :
    canonicalCompletedC3AmbientPortProjection =
      realifiedNaimarkPort ∘L realifiedNaimarkAdjoint := by
  rfl

/-- The completed ambient escape is the ambient identity minus the Naimark
port projection. -/
theorem canonicalCompletedC3AmbientPortEscape_factorization :
    canonicalCompletedC3AmbientPortEscape =
      (1 : RealifiedNaimarkComplexification →L[ℝ]
        RealifiedNaimarkComplexification) -
        canonicalCompletedC3AmbientPortProjection := by
  rfl

/-! ## The exact missing seam and its algebraic consequences -/

/-- Typed interface for a finite-to-completed Naimark crosswalk.

R,V are the finite readout/synthesis pair, U,Ustar are the completed
port/adjoint pair, E is the state-to-ambient embedding, and J transports
finite camera coordinates to the completed camera coordinates.  The two
fields are precisely the readout and synthesis squares; no existence claim
is made by this definition. -/
def NaimarkProjectorIntertwiningSeam
    {𝕜 S A Ainf N : Type*}
    [Ring 𝕜]
    [AddCommGroup S] [AddCommGroup A] [AddCommGroup Ainf] [AddCommGroup N]
    [Module 𝕜 S] [Module 𝕜 A] [Module 𝕜 Ainf] [Module 𝕜 N]
    (E : S →ₗ[𝕜] N) (J : A →ₗ[𝕜] Ainf)
    (R : S →ₗ[𝕜] A) (V : A →ₗ[𝕜] S)
    (U : Ainf →ₗ[𝕜] N) (Ustar : N →ₗ[𝕜] Ainf) : Prop :=
  J.comp R = Ustar.comp E ∧ E.comp V = U.comp J

/-- The readout and synthesis squares imply intertwining of the two
projections V R and U U*. -/
theorem naimarkProjector_intertwines_of_squares
    {𝕜 S A Ainf N : Type*}
    [Ring 𝕜]
    [AddCommGroup S] [AddCommGroup A] [AddCommGroup Ainf] [AddCommGroup N]
    [Module 𝕜 S] [Module 𝕜 A] [Module 𝕜 Ainf] [Module 𝕜 N]
    (E : S →ₗ[𝕜] N) (J : A →ₗ[𝕜] Ainf)
    (R : S →ₗ[𝕜] A) (V : A →ₗ[𝕜] S)
    (U : Ainf →ₗ[𝕜] N) (Ustar : N →ₗ[𝕜] Ainf)
    (hreadout : J.comp R = Ustar.comp E)
    (hsynthesis : E.comp V = U.comp J) :
    E.comp (V.comp R) = (U.comp Ustar).comp E := by
  calc
    E.comp (V.comp R) = (E.comp V).comp R := by
      ext x
      rfl
    _ = (U.comp J).comp R := by rw [hsynthesis]
    _ = U.comp (J.comp R) := by
      ext x
      rfl
    _ = U.comp (Ustar.comp E) := by rw [hreadout]
    _ = (U.comp Ustar).comp E := by
      ext x
      rfl

/-- The seam predicate packages the projector consequence. -/
theorem naimarkProjector_intertwines_of_seam
    {𝕜 S A Ainf N : Type*}
    [Ring 𝕜]
    [AddCommGroup S] [AddCommGroup A] [AddCommGroup Ainf] [AddCommGroup N]
    [Module 𝕜 S] [Module 𝕜 A] [Module 𝕜 Ainf] [Module 𝕜 N]
    (E : S →ₗ[𝕜] N) (J : A →ₗ[𝕜] Ainf)
    (R : S →ₗ[𝕜] A) (V : A →ₗ[𝕜] S)
    (U : Ainf →ₗ[𝕜] N) (Ustar : N →ₗ[𝕜] Ainf)
    (hseam : NaimarkProjectorIntertwiningSeam E J R V U Ustar) :
    E.comp (V.comp R) = (U.comp Ustar).comp E :=
  naimarkProjector_intertwines_of_squares E J R V U Ustar
    hseam.1 hseam.2

/-- Pointwise form of projector intertwining, useful once a concrete
embedding is available. -/
theorem naimarkProjector_intertwines_apply_of_seam
    {𝕜 S A Ainf N : Type*}
    [Ring 𝕜]
    [AddCommGroup S] [AddCommGroup A] [AddCommGroup Ainf] [AddCommGroup N]
    [Module 𝕜 S] [Module 𝕜 A] [Module 𝕜 Ainf] [Module 𝕜 N]
    (E : S →ₗ[𝕜] N) (J : A →ₗ[𝕜] Ainf)
    (R : S →ₗ[𝕜] A) (V : A →ₗ[𝕜] S)
    (U : Ainf →ₗ[𝕜] N) (Ustar : N →ₗ[𝕜] Ainf)
    (hseam : NaimarkProjectorIntertwiningSeam E J R V U Ustar)
    (x : S) :
    E (V (R x)) = U (Ustar (E x)) := by
  have h := congrArg (fun f => f x)
    (naimarkProjector_intertwines_of_seam
      E J R V U Ustar hseam)
  simpa only [LinearMap.comp_apply] using h

/-- The same two squares imply intertwining of the finite complement
I - V R with the completed escape I - U U*. -/
theorem naimarkEscape_intertwines_of_squares
    {𝕜 S A Ainf N : Type*}
    [Ring 𝕜]
    [AddCommGroup S] [AddCommGroup A] [AddCommGroup Ainf] [AddCommGroup N]
    [Module 𝕜 S] [Module 𝕜 A] [Module 𝕜 Ainf] [Module 𝕜 N]
    (E : S →ₗ[𝕜] N) (J : A →ₗ[𝕜] Ainf)
    (R : S →ₗ[𝕜] A) (V : A →ₗ[𝕜] S)
    (U : Ainf →ₗ[𝕜] N) (Ustar : N →ₗ[𝕜] Ainf)
    (hreadout : J.comp R = Ustar.comp E)
    (hsynthesis : E.comp V = U.comp J) :
    E.comp ((LinearMap.id : S →ₗ[𝕜] S) - V.comp R) =
      ((LinearMap.id : N →ₗ[𝕜] N) - U.comp Ustar).comp E := by
  ext x
  change E (x - V (R x)) = E x - U (Ustar (E x))
  rw [map_sub]
  have hp := congrArg (fun f => f x)
    (naimarkProjector_intertwines_of_squares
      E J R V U Ustar hreadout hsynthesis)
  simpa only [LinearMap.comp_apply] using congrArg (fun y => E x - y) hp

/-- The seam predicate packages the escape consequence. -/
theorem naimarkEscape_intertwines_of_seam
    {𝕜 S A Ainf N : Type*}
    [Ring 𝕜]
    [AddCommGroup S] [AddCommGroup A] [AddCommGroup Ainf] [AddCommGroup N]
    [Module 𝕜 S] [Module 𝕜 A] [Module 𝕜 Ainf] [Module 𝕜 N]
    (E : S →ₗ[𝕜] N) (J : A →ₗ[𝕜] Ainf)
    (R : S →ₗ[𝕜] A) (V : A →ₗ[𝕜] S)
    (U : Ainf →ₗ[𝕜] N) (Ustar : N →ₗ[𝕜] Ainf)
    (hseam : NaimarkProjectorIntertwiningSeam E J R V U Ustar) :
    E.comp ((LinearMap.id : S →ₗ[𝕜] S) - V.comp R) =
      ((LinearMap.id : N →ₗ[𝕜] N) - U.comp Ustar).comp E :=
  naimarkEscape_intertwines_of_squares E J R V U Ustar
    hseam.1 hseam.2

/-- Pointwise form of the escape intertwining. -/
theorem naimarkEscape_intertwines_apply_of_seam
    {𝕜 S A Ainf N : Type*}
    [Ring 𝕜]
    [AddCommGroup S] [AddCommGroup A] [AddCommGroup Ainf] [AddCommGroup N]
    [Module 𝕜 S] [Module 𝕜 A] [Module 𝕜 Ainf] [Module 𝕜 N]
    (E : S →ₗ[𝕜] N) (J : A →ₗ[𝕜] Ainf)
    (R : S →ₗ[𝕜] A) (V : A →ₗ[𝕜] S)
    (U : Ainf →ₗ[𝕜] N) (Ustar : N →ₗ[𝕜] Ainf)
    (hseam : NaimarkProjectorIntertwiningSeam E J R V U Ustar)
    (x : S) :
    E (x - V (R x)) = E x - U (Ustar (E x)) := by
  have h := congrArg (fun f => f x)
    (naimarkEscape_intertwines_of_squares
      E J R V U Ustar hseam.1 hseam.2)
  simpa using h

end

end CarrySelfAdjointOperator


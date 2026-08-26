import CarrySelfAdjointOperator.NativeScalarGenuineIdentification
import NativeCarryC3Crosswalk.GeometricCutoffCompleteness
import NativeCarryC3Crosswalk.GenuineBracketGreenIdentity
import Mathlib.Tactic

/-!
# Native bracket, TFVD, and Green from one geometry

The native camera-3 prefix is the scalar readout of the canonical enriched
TFVD port.  The corrected boundary readout of that same port is the reflected
Green form.  Independently, exact head plus whole-center tail recovers the
same camera-free Genuine scalar.

All identities are carry-native.  No external scalar comparison, zero
hypothesis, or prime hypothesis occurs in their statements.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- Exact camera-3 head plus whole-center tail, expressed through the same
Genuine scalar identified term by term with the native bracket. -/
theorem completeNativeC3HeadTail_eq_cpFactor_mul_genuineContinuation
    (cutoff : ℕ) {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    finiteBracketCharacteristic 3 cutoff s +
        (∑' index : ℕ, centerBracketTerm 3 s (index + cutoff)) =
      cpChartFactor 3 s * genuineContinuation s := by
  calc
    finiteBracketCharacteristic 3 cutoff s +
          (∑' index : ℕ, centerBracketTerm 3 s (index + cutoff)) =
        factor 3 s * nativeScalar s :=
      complete_head_add_complete_center_tail_eq_factor_mul_nativeScalar
        (camera := 3) (cutoff := cutoff) (by norm_num) hs
    _ = cpChartFactor 3 s * genuineContinuation s := by
      rw [nativeScalar_eq_genuineContinuation_unconditional]
      have hfactor : factor 3 s = cpChartFactor 3 s := by
        rw [factor_of_odd (by norm_num : 3 ≠ 2) (by norm_num : Odd 3)]
        rfl
      rw [hfactor]

/-- The canonical enriched TFVD state has the native finite bracket as its
scalar readout and the reflected Green form as its corrected boundary readout.
Both coordinates come from the same complete camera-3 geometry. -/
theorem finiteNativeC3BracketTfvdGreen_sameGeometry
    (cutoff : ℕ) (s : ℂ) :
    (finiteSeededEnrichedTfvdGenuineReadout cutoff tfvdHaarScale
          (fun _ : ℕ => (1 : ℂ))
          (canonicalSeededEnrichedTfvdGenuinePort tfvdHaarScale
            (fun _ : ℕ => (1 : ℂ)) s) =
        finiteBracketCharacteristic 3 cutoff s) ∧
    (finiteCanonicalSeededTfvdSameSBoundaryForm cutoff tfvdHaarScale
          (fun _ : ℕ => (1 : ℂ)) s -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 cutoff s =
      greenForm
        (finiteC3GenuineBracketGreenBoundaryPair (3 * cutoff) s)
        (finiteC3GenuineBracketGreenBoundaryPair
          (3 * cutoff) (reflectedParameter s))) := by
  have h := finiteC3GenuineBracketTfvdGreen_capstone
    cutoff tfvdHaarScale_ne_zero (fun _ : ℕ => (1 : ℂ))
      (by intro m; norm_num) s
  exact
    ⟨h.1.trans
        (finiteBracketCharacteristic_three_eq_finiteBracketedDirichletChart
          cutoff s).symm,
      h.2⟩

end

end CarrySelfAdjointOperator

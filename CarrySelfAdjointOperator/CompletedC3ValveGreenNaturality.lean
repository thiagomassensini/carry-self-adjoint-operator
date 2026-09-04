import CarrySelfAdjointOperator.CompletedC3ValveNaturality
import CarrySelfAdjointOperator.CanonicalCompletedC3GammaDslopeGram
import NativeCarryC3Crosswalk.CompletedTfvdGreenIntertwining
import Mathlib.Tactic

/-!
# Completed C3 valve / Green / Gamma naturality

This file assembles the exact cross-stack identifications which are already
proved separately for the canonical completed C3 family.

At a strip parameter `s`:

* the seeded completed TFVD ledger retains the ordinary/log-jet provenance;
* subtracting its provenance boundary gives the intrinsic reflected C3 Green
  form before scalarization;
* the same ledger reconstructs the canonical C3 Green port;
* faithful six-camera packing of that port is exactly the source used by the
  carry Gamma field at centered height;
* the resulting Gamma state is exactly the public ledger-derived Gamma state;
* independently, the same structured one-point C3 state projects to the
  completed scalar boundary pair `(Psi,F)=(-F',F)`.

Thus these are not merely analogous constructions: on the canonical source
locus they are connected by proved equalities.  The only sewing statement not
inserted here is equality of the final Gamma boundary Green form with the
scalar `(F,-F')` Green form.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The completed TFVD boundary, after subtracting provenance, is exactly the
intrinsic C3 Green form written using the port reconstructed from that same
ledger. -/
theorem canonicalCompletedC3ValveLedgerBoundary_eq_intrinsicGreenForm
    (s : ℂ) :
    completedTfvdGreenLedgerSameSBoundary
          (seededCompletedTfvdGreenLedger 1 s) -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 1 s =
      greenForm
        (completedTfvdGreenLedgerC3Port s
          (seededCompletedTfvdGreenLedger 1 s))
        (finiteC3GenuineBracketGreenBoundaryPair
          3 (reflectedParameter s)) := by
  rw [completedTfvdGreenLedgerC3Port_seeded]
  exact completedTfvdGreenLedgerSameSBoundary_sub_provenance_eq_greenForm s

/-- The Green port reconstructed from the canonical ledger is literally the
port used by the structured-state six-camera Gamma source. -/
theorem canonicalCompletedC3ValveLedgerPort_eq_structuredPort
    (s : ℂ) :
    completedTfvdGreenLedgerC3Port s
        (seededCompletedTfvdGreenLedger 1 s) =
      (canonicalCompletedC3StructuredOnePointState
        (centeredHeightParameter s)).greenPort := by
  rw [completedTfvdGreenLedgerC3Port_seeded]
  unfold canonicalCompletedC3StructuredOnePointState
  simp only [operatorHeightParameter_centeredHeightParameter]
  exact (canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket 1 s).symm

/-- After faithful packing, the same ledger port is exactly the six-camera
source fed to Gamma at the centered-height image of `s`. -/
theorem canonicalCompletedC3ValveLedgerCamera_eq_structuredGammaSource
    (s : ℂ) :
    seededCompletedTfvdGreenCameraState s =
      canonicalCompletedC3StructuredGammaSource
        (centeredHeightParameter s) := by
  rw [canonicalCompletedC3StructuredGammaSource_eq_canonical]
  exact (canonicalCompletedC3SixCameraSource_centeredHeightParameter s).symm

/-- The completed scalar chart of the same structured C3 state is exactly
`(-F',F)` at centered height. -/
theorem canonicalCompletedC3ValveStructuredScalarPair_eq_F_negFprime
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3StructuredScalarBoundaryPair
        (centeredHeightParameter s) =
      (completedNativeOperatorBoundaryCompanion
          (centeredHeightParameter s),
        completedNativeOperatorCharacteristic
          (centeredHeightParameter s)) := by
  have hstrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa only [operatorHeightParameter_centeredHeightParameter] using hs
  exact canonicalCompletedC3StructuredScalarBoundaryPair_eq_canonical hstrip

/-- Off the half-abscissa, the Gamma state produced from the same ledger is
literally the canonical completed C3 Gamma state in centered-height
coordinates. -/
theorem canonicalCompletedC3ValveGammaState_eq_ledgerGammaState
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCompletedC3PolarizedGammaState
        (centeredHeightParameter s)
        (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff) =
      seededCompletedTfvdCarryGammaState s hoff := by
  exact canonicalCompletedC3PolarizedGammaState_centeredHeightParameter s hoff

/-- The same ledger-derived Gamma state satisfies the source-relation Green
identity.  This is the Gamma boundary form of the very source whose intrinsic
C3 Green form appears in
`canonicalCompletedC3ValveLedgerBoundary_eq_intrinsicGreenForm`. -/
theorem canonicalCompletedC3ValveGamma_diagonal_green_identity
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    let lambda := carryComplexTimeOfParameter s
    let hlambda : lambda.im ≠ 0 :=
      carryComplexTimeOfParameter_im_ne_zero_of_re_ne_half hoff
    let u := seededCompletedTfvdGreenCameraState s
    let gamma := seededCompletedTfvdCarryGammaState s hoff
    2 * lambda.im *
          (‖gamma.fst‖ ^ 2 + ‖gamma.snd‖ ^ 2) =
      greenForm
          ((allBasesCauchyBlock lambda hlambda u).snd, u.snd)
          ((allBasesCauchyBlock lambda hlambda u).fst, u.fst) -
        greenForm
          ((allBasesCauchyBlock lambda hlambda u).fst, u.fst)
          ((allBasesCauchyBlock lambda hlambda u).snd, u.snd) := by
  exact seededCompletedTfvdCarryGammaState_diagonal_green_identity hoff

/-- One-state, four-chart capstone.  Every conjunct is a previously independent
construction, now stated on one common canonical parameter `s`.

The theorem deliberately stops before asserting the final Gamma--Wronskian
sewing.  Its role is to make the remaining missing arrow type-exact. -/
theorem canonicalCompletedC3ValveGreenNaturality
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    (completedTfvdGreenLedgerSameSBoundary
          (seededCompletedTfvdGreenLedger 1 s) -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 1 s =
      greenForm
        (completedTfvdGreenLedgerC3Port s
          (seededCompletedTfvdGreenLedger 1 s))
        (finiteC3GenuineBracketGreenBoundaryPair
          3 (reflectedParameter s))) ∧
    (seededCompletedTfvdGreenCameraState s =
      canonicalCompletedC3StructuredGammaSource
        (centeredHeightParameter s)) ∧
    (canonicalCompletedC3StructuredScalarBoundaryPair
        (centeredHeightParameter s) =
      (completedNativeOperatorBoundaryCompanion
          (centeredHeightParameter s),
        completedNativeOperatorCharacteristic
          (centeredHeightParameter s))) ∧
    (canonicalCompletedC3PolarizedGammaState
        (centeredHeightParameter s)
        (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff) =
      seededCompletedTfvdCarryGammaState s hoff) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact canonicalCompletedC3ValveLedgerBoundary_eq_intrinsicGreenForm s
  · exact canonicalCompletedC3ValveLedgerCamera_eq_structuredGammaSource s
  · exact canonicalCompletedC3ValveStructuredScalarPair_eq_F_negFprime hs
  · exact canonicalCompletedC3ValveGammaState_eq_ledgerGammaState hoff

end

end CarrySelfAdjointOperator

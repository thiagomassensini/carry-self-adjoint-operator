import CarrySelfAdjointOperator.ConditionalCriticalLineConfinement
import NativeCarryC3Crosswalk.FullEndpointPoissonDefect

/-!
# Canonical enriched C3 port for the completed native operator

The crosswalk already proves that the complete provenance-preserving C3 port
is nonzero at every nonempty cutoff in the open critical strip, even when its
tail-completed scalar readout vanishes.  This file specializes that theorem to
the canonical unit TFVD normalization and to the spectral coordinate of the
completed native operator.

Consequently the final division-free confinement theorem no longer needs a
separate nonvanishing hypothesis for this concrete finite enriched state.  Its
only remaining input is the canonical off-axis Green identity itself.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Minimal nonempty, provenance-preserving C3 port with the canonical unit
TFVD normalization.  No scalar synthesis is used in its definition. -/
def canonicalEnrichedC3SourcePort (s : ℂ) :
    NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3 :=
  (NativeCarryC3Crosswalk.finiteC3EnrichedTfvdPairTransport
      1 (1 : ℂ) (fun _ : ℕ ↦ (1 : ℂ)) s
      (NativeCarryC3Crosswalk.canonicalEnrichedTfvdValueLogJetPair
        (1 : ℂ) (fun _ : ℕ ↦ (1 : ℂ)) s)).greenPort

/-- Tail-completed scalar readout carried by the same enriched pair. -/
def canonicalEnrichedC3TailReadout (s : ℂ) : ℂ :=
  NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout
    1 (1 : ℂ) (fun _ : ℕ ↦ (1 : ℂ)) s

/-- The complete enriched port is nonzero everywhere in the open critical
strip.  This is stronger than nonvanishing only at zeta zeros. -/
theorem canonicalEnrichedC3SourcePort_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalEnrichedC3SourcePort s ≠ 0 := by
  unfold canonicalEnrichedC3SourcePort
  exact NativeCarryC3Crosswalk.canonicalEnrichedTfvdFullStatePort_ne_zero
    1 (by norm_num) (by norm_num)
    (fun _ : ℕ ↦ (1 : ℂ)) (by intro m; norm_num) hs

/-- The scalar readout of the same state is the camera-3 factor times zeta. -/
theorem canonicalEnrichedC3TailReadout_eq_factor_mul_riemannZeta
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalEnrichedC3TailReadout s =
      cpChartFactor 3 s * riemannZeta s := by
  unfold canonicalEnrichedC3TailReadout
  rw [
    NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_factor_mul_genuine
      1 (by norm_num) (fun _ : ℕ ↦ (1 : ℂ))
        (by intro m; norm_num) hs,
    genuineContinuation_eq_riemannZeta hs]

/-- At a zeta zero the scalar readout vanishes, while the complete enriched
state remains nonzero. -/
theorem riemannZeta_zero_tailReadout_zero_and_enrichedPort_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0) :
    canonicalEnrichedC3TailReadout s = 0 ∧
      canonicalEnrichedC3SourcePort s ≠ 0 := by
  constructor
  · rw [canonicalEnrichedC3TailReadout_eq_factor_mul_riemannZeta hs,
      hzero, mul_zero]
  · exact canonicalEnrichedC3SourcePort_ne_zero hs

/-- The same concrete C3 state in the centered height coordinate used by the
self-adjoint operator. -/
def canonicalCompletedOperatorC3State (z : ℂ) :
    NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3 :=
  canonicalEnrichedC3SourcePort (operatorHeightParameter z)

@[simp] theorem canonicalCompletedOperatorC3State_centeredHeightParameter
    (s : ℂ) :
    canonicalCompletedOperatorC3State (centeredHeightParameter s) =
      canonicalEnrichedC3SourcePort s := by
  simp [canonicalCompletedOperatorC3State]

/-- The centered operator state is nonzero throughout the corresponding open
strip, without assuming that the scalar characteristic vanishes. -/
theorem canonicalCompletedOperatorC3State_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedOperatorC3State (centeredHeightParameter s) ≠ 0 := by
  simpa using canonicalEnrichedC3SourcePort_ne_zero hs

/-- Concrete one-obligation capstone.  Nonvanishing is discharged by the
enriched C3 construction; the sole remaining hypothesis is the canonical
off-axis Green identity for that exact state. -/
theorem riemannZeta_zero_re_eq_half_of_canonicalEnrichedC3Port
    (hgreen :
      HasCompletedNativeOperatorOffAxisDiagonalGreenRepresentation
        completedNativeOperatorBoundaryCompanion
        canonicalCompletedOperatorC3State)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0) :
    s.re = 1 / 2 := by
  exact riemannZeta_zero_re_eq_half_of_offAxisDiagonalGreen
    hgreen hs hzero (canonicalCompletedOperatorC3State_ne_zero hs)

end

end CarrySelfAdjointOperator

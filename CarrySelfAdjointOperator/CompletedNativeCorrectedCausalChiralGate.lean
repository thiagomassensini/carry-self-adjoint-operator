import CarrySelfAdjointOperator.CompletedC3CausalChiralBoundaryRelation
import CarrySelfAdjointOperator.CompletedNativeChiralBlockMomentProbe
import CarrySelfAdjointOperator.CompletedNativeSeededClockAtomicGate
import Mathlib.Tactic

/-!
# Corrected native causal/chiral gate

This file packages the already constructed causal/chiral boundary carrier as
the corrected native realization used by the height construction.  It does
not replace the carrier by a positive Gram proxy and it does not reconstruct
the material clock block from Hankel or Jacobi data.

The corrected object keeps the two native readouts separate:

* the completed Wronskian positive chirality;
* the coisometric camera/chiral energy readout.

They are read from the same enriched completed source and are related by the
canonical indefinite boundary form.  The signed chiral coefficient is then
the causal readout whose coefficients are the polarized native moments.
The remaining material gate is precisely the separate same-edge transport
hypothesis consumed by `CompletedNativeSeededClockAtomicGate`.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open C3TraceDynamics

noncomputable section

/-! ## The corrected native carrier -/

/-- The corrected native boundary state is the existing causal/chiral state.
This is only a named interface for the native construction; no new carrier
or normalization is introduced here. -/
def canonicalCompletedNativeCorrectedCausalChiralBoundaryState
    (M : ℕ) (z : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    CanonicalCompletedC3CausalChiralBoundaryCarrier :=
  canonicalCompletedC3CausalChiralBoundaryState M z hzHalf

/-- The enriched completed source produces the corrected native state exactly,
with no coefficient comparison and no Gram/Jacobi reconstruction. -/
theorem canonicalCompletedNativeCorrectedCausalChiralBoundaryState_sourceState
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z
        (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) =
      canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1 := by
  unfold canonicalCompletedNativeCorrectedCausalChiralBoundaryState
  exact canonicalCompletedC3EnrichedCausalChiralBoundaryReadout_sourceState
    M z hzStrip

/-- The corrected native state is independent of the auxiliary Wronskian
cutoff, because both cutoffs are read from the same completed source. -/
theorem canonicalCompletedNativeCorrectedCausalChiralBoundaryState_cutoff_independent
    (M N : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1 =
      canonicalCompletedNativeCorrectedCausalChiralBoundaryState N z hzStrip.1 := by
  unfold canonicalCompletedNativeCorrectedCausalChiralBoundaryState
  exact canonicalCompletedC3CausalChiralBoundaryState_cutoff_independent
    M N z hzStrip

/-- The corrected native datum belongs to the causal boundary relation generated
by the canonical completed source family. -/
theorem canonicalCompletedNativeCorrectedCausalChiralBoundaryState_mem_relation
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1 ∈
      canonicalCompletedC3CausalChiralBoundaryRelation z := by
  unfold canonicalCompletedNativeCorrectedCausalChiralBoundaryState
  exact canonicalCompletedC3CausalChiralBoundaryState_mem_relation M z hzStrip

/-- The native corrected boundary form is the exact coisometric/Wronskian
energy balance, including the correction between the visible and completed
channels. -/
theorem canonicalCompletedNativeCorrectedCausalChiralBoundaryForm_self_eq_energyBalance
    (M : ℕ) (z : ℂ) (hzIm : 0 ≤ z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CausalChiralBoundaryForm
        (canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1)
        (canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1) =
      canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
        M z hzStrip.1 := by
  unfold canonicalCompletedNativeCorrectedCausalChiralBoundaryState
  exact canonicalCompletedC3CausalChiralBoundaryForm_self_eq_energyBalance
    M z hzIm hzStrip

/-- The corrected native state is isotropic exactly when the native energy
balance vanishes. -/
theorem canonicalCompletedNativeCorrectedCausalChiralBoundaryState_isotropic_iff_energyBalance
    (M : ℕ) (z : ℂ) (hzIm : 0 ≤ z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CausalChiralBoundaryForm
        (canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1)
        (canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1) = 0 ↔
      canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
        M z hzStrip.1 = 0 := by
  unfold canonicalCompletedNativeCorrectedCausalChiralBoundaryState
  exact canonicalCompletedC3CausalChiralBoundaryStateIsotropic_iff_energyBalance
    M z hzIm hzStrip

/-! ## The corrected native chiral readout -/

/-- The corrected native scalar coefficient is the signed positive-minus-
negative chiral boundary readout.  It is defined before any Hankel or Jacobi
construction. -/
def canonicalCompletedNativeCorrectedChiralBoundaryCoefficient
    (M p : ℕ) : ℂ :=
  canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M (p + 1)

theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_response
    (M p : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
      canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient M (p + 1) := by
  unfold canonicalCompletedNativeCorrectedChiralBoundaryCoefficient
  exact canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient_eq_response
    M (p + 1)

/-- Every coefficient of the corrected native readout is the corresponding
polarized native Green moment. -/
theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_polarizedMoment
    (M p q : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M (p + q) =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q := by
  unfold canonicalCompletedNativeCorrectedChiralBoundaryCoefficient
  exact canonicalCompletedC3ChiralBlockSignature_succ_eq_polarizedMoment M p q

/-- Odd coefficients of the corrected native readout recover the canonical
native logarithmic moments. -/
theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_odd_eq_canonicalMoment
    (M n : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M (2 * n) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  unfold canonicalCompletedNativeCorrectedChiralBoundaryCoefficient
  exact canonicalCompletedC3ChiralBlockSignature_odd_eq_canonicalMoment M n

/-! ## The exact interface with the material clock gate -/

/-- If the independently defined material clock satisfies the exact same-edge
transport hypothesis, its first column is this corrected native chiral
readout.  This theorem deliberately does not manufacture that hypothesis. -/
theorem seededClockAtlasCoefficient_firstColumn_eq_correctedNativeChiralBoundaryCoefficient_of_sameEdgeTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) (p : ℕ)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block) :
    seededClockAtlasCoefficient block p 0 =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p := by
  unfold canonicalCompletedNativeCorrectedChiralBoundaryCoefficient
  exact seededClockAtlasCoefficient_firstColumn_eq_chiralBlockSignature_of_sameEdgeTransport
    M block p htransport

/-! ## One packaged source-level gate -/

/-- All source-level obligations of the corrected native construction that are
already formalized: common-source identification, relation membership and
cutoff independence.  The remaining material clock calibration is kept as
the separate `HasSameEdgeGreenToClockBoundaryTransport` hypothesis. -/
theorem canonicalCompletedNativeCorrectedCausalChiralBoundaryGate
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z
        (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) =
      canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1 ∧
    canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1 ∈
      canonicalCompletedC3CausalChiralBoundaryRelation z ∧
    ∀ N : ℕ,
      canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1 =
        canonicalCompletedNativeCorrectedCausalChiralBoundaryState N z hzStrip.1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact canonicalCompletedNativeCorrectedCausalChiralBoundaryState_sourceState
      M z hzStrip
  · exact canonicalCompletedNativeCorrectedCausalChiralBoundaryState_mem_relation
      M z hzStrip
  · intro N
    exact canonicalCompletedNativeCorrectedCausalChiralBoundaryState_cutoff_independent
      M N z hzStrip

end

end CarrySelfAdjointOperator

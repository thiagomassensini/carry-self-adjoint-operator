import CarrySelfAdjointOperator.BR2IncidenceStrictPositivity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

/-!
# Dimensional obstruction for a generic completed Green-jet transport

The completed native transport abbreviation is polymorphic in the
archimedean Hilbert carrier and its state.  Consequently it cannot have an
unconditional constructor at that level of generality: choosing the
one-dimensional carrier `ℂ` makes the complete target finite-dimensional,
whereas any supported bracket transport forces an infinite linearly
independent even jet family.

This result does not obstruct a transport into a fixed infinite-dimensional
completed TFVD/Green carrier.  It records why that concrete carrier and its
state must be part of the final bridge rather than left arbitrary.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera

noncomputable section

local instance : InnerProductSpace ℝ ℂ :=
  InnerProductSpace.rclikeToReal ℂ ℂ

/-- A supported all-order incidence transport forces its completed Green-jet
target to be infinite-dimensional.  In particular, no such transport exists
when the target carries a `Module.Finite` instance. -/
theorem not_nonempty_canonicalCompletedNativeBR2IncidenceJetTransport_of_moduleFinite
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    [Module.Finite ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier)]
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (xiState : ℂ → Hxi) :
    ¬ Nonempty
      (CanonicalCompletedNativeBR2IncidenceJetTransport
        base radius xiState) := by
  rintro ⟨transport⟩
  have hli := transport.even_linearIndependent
    hbase hradius
  exact
    (Module.Finite.not_linearIndependent_of_infinite
      (fun n : ℕ ↦
        completedGreenParityJet
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic
            (completedNativeC3ProductLedgerState
              xiState))
          (Sum.inl n))) hli

/-- The generic abbreviation is already impossible for every state on the
one-dimensional archimedean carrier `ℂ`, because its complete product carrier
is finite-dimensional over `ℝ`. -/
theorem not_nonempty_canonicalCompletedNativeBR2IncidenceJetTransport_complex
    (xiState : ℂ → ℂ) :
    ¬ Nonempty
      (CanonicalCompletedNativeBR2IncidenceJetTransport
        2 1 xiState) := by
  exact
    not_nonempty_canonicalCompletedNativeBR2IncidenceJetTransport_of_moduleFinite
      (show IsSupported 2 by norm_num [IsSupported])
      (show 1 ∈ radiusSet 2 by norm_num [radiusSet, halfRange])
      xiState

/-- An all-order incidence transport into the actual completed Green jets
forces complex differentiability of the whole normalized product state at the
Taylor center.  A real-linear packaging equivalence alone cannot discharge
this condition: if complex differentiability fails, Lean's first complex
iterated derivative is zero, contradicting odd-jet independence. -/
theorem
    normalizedCompletedNativeC3ProductLedger_differentiableAt_zero_of_incidenceTransport
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (xiState : ℂ → Hxi)
    (transport : CanonicalCompletedNativeBR2IncidenceJetTransport
      base radius xiState) :
    DifferentiableAt ℂ
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        (completedNativeC3ProductLedgerState xiState)) 0 := by
  by_contra hdiff
  have hzero :
      completedGreenParityJet
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic
            (completedNativeC3ProductLedgerState xiState))
          (Sum.inr 0) = 0 := by
    simp only [completedGreenParityJet, Nat.mul_zero, zero_add]
    unfold completedGreenTaylorJet
    rw [show iteratedDeriv 1
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic
            (completedNativeC3ProductLedgerState xiState)) 0 = 0 by
      simpa [iteratedDeriv_one] using
        (deriv_zero_of_not_differentiableAt hdiff)]
    simp
  exact (transport.odd_linearIndependent hbase hradius).ne_zero 0 hzero

end

end CarrySelfAdjointOperator

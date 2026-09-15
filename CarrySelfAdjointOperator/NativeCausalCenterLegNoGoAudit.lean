import CarrySelfAdjointOperator.CompletedNativeHPGateAudit
import CarrySelfAdjointOperator.ProjectiveValveCarryGreenObstruction

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The raw zero-seed canonical C3 causal response cannot satisfy the
center--leg readout required by the corrected HP carrier.  The incidence
side-condition is automatic for every `BR2CameraIncidence`; the obstruction
is the translated response family itself, not a missing diagonal case. -/
theorem not_canonicalBR2CausalGreenResponse_centerLegReadout
    (incidence : BR2CameraIncidence) :
    ¬ HasCanonicalCompletedNativeTfvdGreenCenterLegReadout incidence
      (canonicalBR2CameraBracketCausalGreenResponseParityJet 3 1) := by
  intro hreadout
  let u : ℕ → CanonicalCompletedTfvdGreenHilbertCarrier :=
    br2CameraBracketCausalGreenResponse
      (canonicalBR2CarryAmplitudeRatio 3) 3 1
  have harray : ∀ p q : ℕ,
      polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment p q =
        inner ℂ (u p) (u q) := by
    intro p q
    rcases Nat.even_or_odd' p with ⟨i, rfl | rfl⟩
    · rcases Nat.even_or_odd' q with ⟨j, rfl | rfl⟩
      · simpa [u, canonicalBR2CameraBracketCausalGreenResponseParityJet,
          br2CameraBracketCausalGreenResponseParityJet, parityJetNumber] using
          hreadout (Sum.inl i) (Sum.inl j)
            (incidence.centerCoordinate_ne_legCoordinate (Sum.inl i) (Sum.inl j))
      · simpa [u, canonicalBR2CameraBracketCausalGreenResponseParityJet,
          br2CameraBracketCausalGreenResponseParityJet, parityJetNumber] using
          hreadout (Sum.inl i) (Sum.inr j)
            (incidence.centerCoordinate_ne_legCoordinate (Sum.inl i) (Sum.inr j))
    · rcases Nat.even_or_odd' q with ⟨j, rfl | rfl⟩
      · simpa [u, canonicalBR2CameraBracketCausalGreenResponseParityJet,
          br2CameraBracketCausalGreenResponseParityJet, parityJetNumber] using
          hreadout (Sum.inr i) (Sum.inl j)
            (incidence.centerCoordinate_ne_legCoordinate (Sum.inr i) (Sum.inl j))
      · simpa [u, canonicalBR2CameraBracketCausalGreenResponseParityJet,
          br2CameraBracketCausalGreenResponseParityJet, parityJetNumber] using
          hreadout (Sum.inr i) (Sum.inr j)
            (incidence.centerCoordinate_ne_legCoordinate (Sum.inr i) (Sum.inr j))
  have hcoeff : IsPolarizedGreenCoefficientEquation
      canonicalCompletedNativeLogDerivativeMoment
      (fun p q => inner ℂ (u p) (u q)) := by
    have hfun :
        (fun p q => inner ℂ (u p) (u q)) =
          polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment := by
      funext p q
      exact (harray p q).symm
    rw [hfun]
    exact polarizedGreenMomentCoefficient_coefficientEquation
      canonicalCompletedNativeLogDerivativeMoment
  apply not_br2C3CausalResponse_coefficientEquation
    (canonicalBR2CarryAmplitudeRatio 3)
    (canonicalBR2CarryAmplitudeRatio_pos (by norm_num [IsSupported]))
    (canonicalBR2CarryAmplitudeRatio_lt_one (by norm_num [IsSupported]))
    canonicalCompletedNativeLogDerivativeMoment
  simpa [u] using hcoeff

end
end CarrySelfAdjointOperator

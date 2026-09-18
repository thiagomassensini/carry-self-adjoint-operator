import CarrySelfAdjointOperator.CompletedC3SymplecticGammaState

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The completed C3 state at the conjugate centered height is the existing
camera-3 Genuine Green pair at the reflected spectral parameter. -/
theorem canonicalCompletedOperatorC3State_conj (w : ℂ) :
    canonicalCompletedOperatorC3State (conj w) =
      NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
        (reflectedParameter (operatorHeightParameter w)) := by
  rw [canonicalCompletedOperatorC3State,
    operatorHeightParameter_conj_eq_reflectedParameter,
    canonicalEnrichedC3SourcePort_eq_greenBoundaryPair]

/-- Reflection ledger for the `z, conj w` readout.  The second parenthesis is
left as the explicit reflected-source difference. -/
theorem canonicalCompletedC3SymplecticCameraComplexGreenReadout_z_conj_w_decomposition
    (z w : ℂ) :
    canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w) =
      greenForm (𝕜 := ℂ)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
          (operatorHeightParameter z))
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
          (operatorHeightParameter w)) +
      (greenForm (𝕜 := ℂ)
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter z))
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (reflectedParameter (operatorHeightParameter w))) -
        greenForm (𝕜 := ℂ)
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter z))
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter w))) := by
  rw [canonicalCompletedC3SymplecticCameraComplexGreenReadout_eq_greenForm]
  simp only [canonicalCompletedOperatorC3State]
  rw [operatorHeightParameter_conj_eq_reflectedParameter,
    canonicalEnrichedC3SourcePort_eq_greenBoundaryPair,
    canonicalEnrichedC3SourcePort_eq_greenBoundaryPair]
  ring

/-- Reflection ledger for the `w, conj z` readout.  The reflected-source
difference is retained explicitly and is not assumed to vanish. -/
theorem canonicalCompletedC3SymplecticCameraComplexGreenReadout_w_conj_z_decomposition
    (z w : ℂ) :
    canonicalCompletedC3SymplecticCameraComplexGreenReadout w (conj z) =
      greenForm (𝕜 := ℂ)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
          (operatorHeightParameter w))
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
          (operatorHeightParameter z)) +
      (greenForm (𝕜 := ℂ)
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter w))
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (reflectedParameter (operatorHeightParameter z))) -
        greenForm (𝕜 := ℂ)
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter w))
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter z))) := by
  rw [canonicalCompletedC3SymplecticCameraComplexGreenReadout_eq_greenForm]
  simp only [canonicalCompletedOperatorC3State]
  rw [operatorHeightParameter_conj_eq_reflectedParameter,
    canonicalEnrichedC3SourcePort_eq_greenBoundaryPair,
    canonicalEnrichedC3SourcePort_eq_greenBoundaryPair]
  ring

end

end CarrySelfAdjointOperator

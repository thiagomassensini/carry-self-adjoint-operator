import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundaryStieltjesGate
import CarrySelfAdjointOperator.CompletedNativeGeometryHeightProvenance

/-! Conditional handoff to the EXISTING camera/Jacobi/height capstone.
The raw all-order strict boundary inequality remains the sole input. -/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

/-- No operator is rebuilt: the elementary raw boundary sign feeds the old
native-geometry height chain through the proved parity equivalence. -/
theorem nativeGeometry_to_finiteHeight_chain_of_evenBoundary
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff N : ℕ)
    (hboundary : ∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      normalizedCompletedNativeCameraCharacteristic camera cutoff =
          (fun time : ℝ => completedNativeOperatorCharacteristic (time : ℂ)) ∧
      completedNativeCameraLogDerivativeMoment camera cutoff =
          canonicalCompletedNativeLogDerivativeMoment ∧
      (∃ hgram :
          (hankelGram (completedNativeCameraLogDerivativeMoment camera cutoff) N).PosDef,
        canonicalFiniteJacobiSection
          (completedNativeCameraLogDerivativeMoment camera cutoff) N hgram =
            canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
      (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  let hpos := nativeSourceEvenBoundary_positive_iff_stieltjes.mp hboundary
  exact ⟨hpos,nativeGeometry_to_finiteHeight_chain hcamera cutoff N hpos⟩
end
end CarrySelfAdjointOperator

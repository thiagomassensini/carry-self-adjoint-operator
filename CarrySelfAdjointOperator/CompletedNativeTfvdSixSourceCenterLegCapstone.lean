import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceCenterLegBridge
import CarrySelfAdjointOperator.CompletedNativeCorrectedGeometryHeightProvenance

/-!
# Six-source TFVD center--leg downstream conditional capstone

This file records the exact downstream consequence that would follow from
vanishing of the explicit defect isolated in
`CompletedNativeTfvdSixSourceCenterLegBridge`.  It is deliberately a
conditional composition: the companion bridge proves that the literal BR2
projective carrier has a nonzero order-zero defect, so this theorem is not a
claim that its premise holds.  No moment matrix is used to define a carrier,
and no additional analytic or positivity premise is introduced.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera

noncomputable section

/-- Counterfactually, vanishing of the explicit enriched six-source
center--leg defect would give the pre-existing finite-height chain.  The only
non-composite input is the typed entrywise equality from the material
coefficient to the projective Hilbert pairing; BR2 incidence supplies
strictness.  The bridge's order-zero no-go shows that this premise is false
for the literal projective jet. -/
theorem nativeC3SeededClockTfvdSixSource_defect_eq_zero_to_finiteHeightChain
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (side : CameraLegSide)
    (hdefect : ∀ i j : ℕ ⊕ ℕ,
      (canonicalParityCenterLegIncidence
          base radius hbase hradius side).centerCoordinate i ≠
        (canonicalParityCenterLegIncidence
          base radius hbase hradius side).legCoordinate j →
      nativeC3SeededClockTfvdSixSourceCenterLegDefect
        M q hqpos.le hq1 S base radius i j = 0)
    (cutoff N : ℕ) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      normalizedCompletedNativeCameraCharacteristic 2 cutoff =
          (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
        completedNativeCameraLogDerivativeMoment 2 cutoff =
          canonicalCompletedNativeLogDerivativeMoment ∧
        (∃ hgram :
            (hankelGram
              (completedNativeCameraLogDerivativeMoment 2 cutoff) N).PosDef,
          canonicalFiniteJacobiSection
              (completedNativeCameraLogDerivativeMoment 2 cutoff) N hgram =
            canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
        (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  let incidence : BR2CameraIncidence :=
    canonicalParityCenterLegIncidence base radius hbase hradius side
  have hreadout :
      HasCanonicalCompletedNativeTfvdGreenCenterLegReadout incidence
        (br2CameraBracketProjectiveHilbertParityJet base radius) :=
    (nativeC3SeededClockTfvdSixSource_centerLegReadout_iff_defect_eq_zero
      M q hqpos hq1 S base radius incidence).mpr hdefect
  exact canonicalC2Geometry_height_chain_of_tfvdGreenCenterLegReadout
    hbase hradius
    (br2CameraBracketProjectiveHilbertIncidenceJetTransport base radius)
    incidence hreadout cutoff N

end

end CarrySelfAdjointOperator

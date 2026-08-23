import CarrySelfAdjointOperator.CompletedTfvdCanonicalSourceIntertwining
import CarrySelfAdjointOperator.CarryGammaState
import NativeCarryC3Crosswalk.CompletedTfvdGreenIntertwining

/-!
# Literal identity of the private and public completed C3 gamma states

The completed-TFVD source intertwiner already proves that the private
six-camera source is the public source reconstructed from the uncollapsed
ordinary/log-jet ledger.  This file transports that literal source equality
through the already-defined gamma field.

No scalar Wronskian identity is assumed here.  The result concerns only the
operatorial state and its strictly positive diagonal energy.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Off the half-abscissa, the centered height parameter is nonreal. -/
theorem centeredHeightParameter_im_ne_zero_of_re_ne_half
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    (centeredHeightParameter s).im ≠ 0 := by
  rw [centeredHeightParameter_im]
  intro hzero
  apply hoff
  linarith

/-- The total gamma state used by the private operator is literally the
public gamma state obtained from the completed TFVD ledger. -/
theorem canonicalTotalCarryGammaState_centeredHeightParameter_eq_seeded
    (s : ℂ) (hoff : s.re ≠ (1 : ℝ) / 2) :
    totalCarryGammaState canonicalCompletedC3SixCameraSource
        (centeredHeightParameter s) =
      NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState s hoff := by
  have hz : (centeredHeightParameter s).im ≠ 0 :=
    centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
  rw [totalCarryGammaState_of_im_ne_zero
    canonicalCompletedC3SixCameraSource hz]
  unfold NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState
  rw [canonicalCompletedC3SixCameraSource_centeredHeightParameter]
  simp [carryComplexTimeOfParameter_eq_centeredHeightParameter]

/-- Therefore the private total gamma state is nonzero at every off-critical
point of the open strip. -/
theorem canonicalTotalCarryGammaState_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    totalCarryGammaState canonicalCompletedC3SixCameraSource
        (centeredHeightParameter s) ≠ 0 := by
  rw [canonicalTotalCarryGammaState_centeredHeightParameter_eq_seeded s hoff]
  exact NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState_ne_zero
    hs hoff

/-- The strictly positive public gamma energy is exactly the energy of the
private total gamma state, not merely an analogous quantity. -/
theorem canonicalTotalCarryGammaEnergy_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    0 <
      ‖(totalCarryGammaState canonicalCompletedC3SixCameraSource
          (centeredHeightParameter s)).fst‖ ^ 2 +
        ‖(totalCarryGammaState canonicalCompletedC3SixCameraSource
          (centeredHeightParameter s)).snd‖ ^ 2 := by
  rw [canonicalTotalCarryGammaState_centeredHeightParameter_eq_seeded s hoff]
  exact NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaEnergy_pos
    hs hoff

end

end CarrySelfAdjointOperator

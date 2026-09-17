import CarrySelfAdjointOperator.FiveFieldCapstoneChannels

/-!
The final physical bridge is split into the two minimal obligations exposed by
the research artifacts: a decomposition of the physical tensor and a
crosswalk identifying its Green and Stokes channel vectors.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

def FiveFieldPhysicalDecomposition
    (cubicTauTensor : CubicTensor)
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (greenChannels stokesChannels : SixChannels) : Prop :=
  cubicTauTensor =
    endpoint
      + threeGreenReadout πc t1 t2 greenChannels
      + stokesNormalReadout stokesChannels

def FiveFieldChannelCrosswalk
    (greenChannels stokesChannels : SixChannels)
    (q : FiveScalarFieldState) : Prop :=
  greenChannels = q.toChannelState.threeGreen ∧
    stokesChannels = q.toChannelState.stokes

theorem cubicTauTensor_eq_fiveScalarFieldReadout_of_decomposition
    (cubicTauTensor : CubicTensor)
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (greenChannels stokesChannels : SixChannels)
    (q : FiveScalarFieldState)
    (hdecomp : FiveFieldPhysicalDecomposition cubicTauTensor πc t1 t2
      endpoint greenChannels stokesChannels)
    (hcrosswalk : FiveFieldChannelCrosswalk greenChannels stokesChannels q) :
    cubicTauTensor = fiveScalarFieldReadout πc t1 t2 endpoint q := by
  rcases hcrosswalk with ⟨hgreen, hstokes⟩
  calc
    cubicTauTensor =
        endpoint
          + threeGreenReadout πc t1 t2 greenChannels
          + stokesNormalReadout stokesChannels := hdecomp
    _ = endpoint
          + threeGreenReadout πc t1 t2 q.toChannelState.threeGreen
          + stokesNormalReadout q.toChannelState.stokes := by
      rw [hgreen, hstokes]
    _ = fiveScalarFieldReadout πc t1 t2 endpoint q := by
      rfl

theorem FiveFieldReadoutBridge_of_decomposition_and_crosswalk
    (cubicTauTensor : CubicTensor)
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (greenChannels stokesChannels : SixChannels)
    (q : FiveScalarFieldState) :
    FiveFieldPhysicalDecomposition cubicTauTensor πc t1 t2 endpoint
        greenChannels stokesChannels ∧
      FiveFieldChannelCrosswalk greenChannels stokesChannels q →
      FiveFieldReadoutBridge cubicTauTensor πc t1 t2 endpoint q := by
  intro h
  exact cubicTauTensor_eq_fiveScalarFieldReadout_of_decomposition
    cubicTauTensor πc t1 t2 endpoint greenChannels stokesChannels q h.1 h.2

end
end NativeCarryFiveFieldCapstone

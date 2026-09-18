import CarrySelfAdjointOperator.FiveFieldCapstoneMinimal

/-!
The final notes describe five scalar fields but twelve readout channels.  This
file makes that packaging explicit, without pretending that the analytic
fields or their endpoint integrals have already been formalized.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

structure FiveScalarFieldState where
  yplus : ℂ
  yminus : ℂ
  c1 : ℂ
  x1 : ℂ
  c2 : ℂ
  x2 : ℂ
  s10 : ℂ
  s11 : ℂ
  s12 : ℂ
  s20 : ℂ
  s21 : ℂ
  s22 : ℂ

def FiveScalarFieldState.toChannelState
    (q : FiveScalarFieldState) : FiveFieldChannelState :=
  { threeGreen := ![q.yplus, q.yminus, q.c1, q.x1, q.c2, q.x2]
    stokes := ![q.s10, q.s11, q.s12, q.s20, q.s21, q.s22] }

@[simp] theorem FiveScalarFieldState.toChannelState_threeGreen
    (q : FiveScalarFieldState) (i : Fin 6) :
    q.toChannelState.threeGreen i =
      ![q.yplus, q.yminus, q.c1, q.x1, q.c2, q.x2] i := by
  rfl

@[simp] theorem FiveScalarFieldState.toChannelState_stokes
    (q : FiveScalarFieldState) (i : Fin 6) :
    q.toChannelState.stokes i =
      ![q.s10, q.s11, q.s12, q.s20, q.s21, q.s22] i := by
  rfl

def fiveScalarFieldReadout
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (q : FiveScalarFieldState) : CubicTensor :=
  capstoneRHS πc t1 t2 endpoint q.toChannelState

def FiveFieldReadoutBridge
    (cubicTauTensor : CubicTensor)
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (q : FiveScalarFieldState) : Prop :=
  cubicTauTensor = fiveScalarFieldReadout πc t1 t2 endpoint q

theorem FiveFieldReadoutBridge_iff_explicit
    (cubicTauTensor : CubicTensor)
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (q : FiveScalarFieldState) :
    FiveFieldReadoutBridge cubicTauTensor πc t1 t2 endpoint q ↔
      cubicTauTensor =
        endpoint
          + threeGreenReadout πc t1 t2 q.toChannelState.threeGreen
          + stokesNormalReadout q.toChannelState.stokes := by
  rfl

theorem cubicTauTensor_eq_fiveScalarFieldReadout_of_bridge
    (cubicTauTensor : CubicTensor)
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (q : FiveScalarFieldState)
    (hbridge : FiveFieldReadoutBridge cubicTauTensor πc t1 t2 endpoint q) :
    cubicTauTensor = fiveScalarFieldReadout πc t1 t2 endpoint q :=
  hbridge

end
end NativeCarryFiveFieldCapstone

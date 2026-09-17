import Mathlib

/-!
Minimal formal layer extracted from the final five-field capstone notes.

This file deliberately formalizes only the exact finite-dimensional readout
algebra.  The analytic bridge from the physical cubic tau tensor to this
readout is kept as an explicit hypothesis in the final theorem below.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

abbrev CubicTensor := Fin 4 → ℂ
abbrev SixChannels := Fin 6 → ℂ

structure FiveFieldChannelState where
  threeGreen : SixChannels
  stokes : SixChannels

def threeGreenReadoutMatrix (t1 t2 : ℂ) : Matrix (Fin 4) (Fin 6) ℂ :=
  !![
    0, 0, -32 / 363, -2656 / (35937 * t1), 0, 0;
    2 / 121, 0, -4 / 121, -268 / (11979 * t1), 0, 64 / (11979 * t2);
    0, 8 / 363, 0, 8 / (1331 * t1), -16 / 363, -128 / (3993 * t2);
    0, 0, 0, 0, -18 / 121, -171 / (1331 * t2)
  ]

def stokesNormalReadoutMatrix : Matrix (Fin 4) (Fin 6) ℂ :=
  !![
    128 / 1089, -16 / 33, 0, 0, 0, 0;
    32 / 363, 0, 0, 128 / 3267, -16 / 99, 0;
    6 / 121, 0, -2 / 11, 32 / 363, 0, 0;
    0, 0, 0, 18 / 121, 0, -6 / 11
  ]

def threeGreenCoefficientReadout
    (t1 t2 : ℂ) (z : SixChannels) : CubicTensor :=
  ![
    (-32 / 363 : ℂ) * z 2 - (2656 / (35937 * t1)) * z 3,
    (2 / 121 : ℂ) * z 0 - (4 / 121 : ℂ) * z 2
      - (268 / (11979 * t1)) * z 3 + (64 / (11979 * t2)) * z 5,
    (8 / 363 : ℂ) * z 1 + (8 / (1331 * t1)) * z 3
      - (16 / 363 : ℂ) * z 4 - (128 / (3993 * t2)) * z 5,
    (-18 / 121 : ℂ) * z 4 - (171 / (1331 * t2)) * z 5
  ]

def threeGreenReadout
    (πc t1 t2 : ℂ) (z : SixChannels) : CubicTensor :=
  (Complex.I / (4 * πc^3)) • threeGreenCoefficientReadout t1 t2 z

def stokesNormalReadout (s : SixChannels) : CubicTensor :=
  ![
    (128 / 1089 : ℂ) * s 0 - (16 / 33 : ℂ) * s 1,
    (32 / 363 : ℂ) * s 0 + (128 / 3267 : ℂ) * s 3
      - (16 / 99 : ℂ) * s 4,
    (6 / 121 : ℂ) * s 0 - (2 / 11 : ℂ) * s 2
      + (32 / 363 : ℂ) * s 3,
    (18 / 121 : ℂ) * s 3 - (6 / 11 : ℂ) * s 5
  ]

def capstoneRHS
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (state : FiveFieldChannelState) : CubicTensor :=
  endpoint
    + threeGreenReadout πc t1 t2 state.threeGreen
    + stokesNormalReadout state.stokes

theorem threeGreenCoefficientReadout_eq_mulVec
    (t1 t2 : ℂ) (z : SixChannels) :
    threeGreenCoefficientReadout t1 t2 z =
      Matrix.mulVec (threeGreenReadoutMatrix t1 t2) z := by
  funext i
  fin_cases i <;>
    simp [threeGreenCoefficientReadout, threeGreenReadoutMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring

theorem threeGreenReadout_eq_scalar_smul_mulVec
    (πc t1 t2 : ℂ) (z : SixChannels) :
    threeGreenReadout πc t1 t2 z =
      (Complex.I / (4 * πc^3)) •
        (Matrix.mulVec (threeGreenReadoutMatrix t1 t2) z) := by
  rw [threeGreenReadout, threeGreenCoefficientReadout_eq_mulVec]

theorem stokesNormalReadout_eq_mulVec
    (s : SixChannels) :
    stokesNormalReadout s = Matrix.mulVec stokesNormalReadoutMatrix s := by
  funext i
  fin_cases i <;>
    simp [stokesNormalReadout, stokesNormalReadoutMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  <;> ring

theorem capstoneRHS_eq_endpoint_add_readouts
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (state : FiveFieldChannelState) :
    capstoneRHS πc t1 t2 endpoint state =
      endpoint
        + threeGreenReadout πc t1 t2 state.threeGreen
        + stokesNormalReadout state.stokes := by
  rfl

/-- The only missing bridge in the notes is isolated as an explicit premise. -/
theorem cubicTauTensor_eq_fiveFieldReadout_of_bridge
    (cubicTauTensor : CubicTensor)
    (πc t1 t2 : ℂ)
    (endpoint : CubicTensor)
    (state : FiveFieldChannelState)
    (hbridge : cubicTauTensor =
      endpoint
        + threeGreenReadout πc t1 t2 state.threeGreen
        + stokesNormalReadout state.stokes) :
    cubicTauTensor = capstoneRHS πc t1 t2 endpoint state := by
  simpa [capstoneRHS] using hbridge

end
end NativeCarryFiveFieldCapstone

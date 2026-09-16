import CarrySelfAdjointOperator.FiveFieldCapstoneMinimal

/-!
Exact algebra behind the Stokes-normal matrix in the final capstone notes.
The cumulative channels are kept abstract; only the quadratic opening data and
their cubic polarization are formalized here.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

def stokesGammaNeg (v1 v2 : ℂ) : ℂ :=
  (-400 / 1089 : ℂ) * v1^2
    + (32 / 121 : ℂ) * v1 * v2
    - (48 / 121 : ℂ) * v2^2

def stokesGammaZero (v1 v2 : ℂ) : ℂ :=
  (-16 / 33 : ℂ) * v1^2 - (6 / 11 : ℂ) * v2^2

def stokesGammaOne (v2 : ℂ) : ℂ :=
  (-6 / 11 : ℂ) * v2^2

def stokesCumulativeReadout (v1 v2 : ℂ) (s : SixChannels) : ℂ :=
  (stokesGammaNeg v1 v2 - stokesGammaZero v1 v2) *
      (v1 * s 0 + v2 * s 3) +
    (stokesGammaZero v1 v2 - stokesGammaOne v2) *
      (v1 * s 1 + v2 * s 4) +
    stokesGammaOne v2 * (v1 * s 2 + v2 * s 5)

def cubicPolarization (T : CubicTensor) (v1 v2 : ℂ) : ℂ :=
  T 0 * v1^3 + 3 * T 1 * v1^2 * v2 +
    3 * T 2 * v1 * v2^2 + T 3 * v2^3

theorem stokesCumulativeReadout_eq_cubicPolarization
    (v1 v2 : ℂ) (s : SixChannels) :
    stokesCumulativeReadout v1 v2 s =
      cubicPolarization (stokesNormalReadout s) v1 v2 := by
  simp [stokesCumulativeReadout, stokesGammaNeg, stokesGammaZero,
    stokesGammaOne, cubicPolarization, stokesNormalReadout]
  ring

theorem stokesGammaNeg_sub_zero
    (v1 v2 : ℂ) :
    stokesGammaNeg v1 v2 - stokesGammaZero v1 v2 =
      (128 / 1089 : ℂ) * v1^2 +
        (32 / 121 : ℂ) * v1 * v2 +
        (18 / 121 : ℂ) * v2^2 := by
  simp [stokesGammaNeg, stokesGammaZero]
  ring

theorem stokesGammaZero_sub_one
    (v1 v2 : ℂ) :
    stokesGammaZero v1 v2 - stokesGammaOne v2 =
      (-16 / 33 : ℂ) * v1^2 := by
  simp [stokesGammaZero, stokesGammaOne]
  ring

end
end NativeCarryFiveFieldCapstone

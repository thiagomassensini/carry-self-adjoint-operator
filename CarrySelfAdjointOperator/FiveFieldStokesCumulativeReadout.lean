import CarrySelfAdjointOperator.FiveFieldStokesCumulativeAlgebra

/-!
The two complete Stokes fields are packed into six cumulative channels.
This file records only the algebraic passage between that packing and the
single direction `v₁ f₁ + v₂ f₂`; no analytic or physical identification is
asserted here.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

open MeasureTheory

def stokesCumulativePair
    (s1 s2 : Fin 3 → ℂ) : SixChannels :=
  ![s1 0, s1 1, s1 2, s2 0, s2 1, s2 2]

def stokesGammaCumulativeReadout
    (v1 v2 : ℂ) (s : Fin 3 → ℂ) : ℂ :=
  (stokesGammaNeg v1 v2 - stokesGammaZero v1 v2) * s 0 +
    (stokesGammaZero v1 v2 - stokesGammaOne v2) * s 1 +
    stokesGammaOne v2 * s 2

def stokesCumulativeFieldPair
    (f1 f2 : ℝ → ℂ) (t1 t2 : ℝ) : SixChannels :=
  stokesCumulativePair
    (stokesCumulativeChannels f1 t1 t2)
    (stokesCumulativeChannels f2 t1 t2)

theorem stokesCumulativeReadout_pair_eq_gammaCumulativeReadout
    (v1 v2 : ℂ) (s1 s2 : Fin 3 → ℂ) :
    stokesCumulativeReadout v1 v2 (stokesCumulativePair s1 s2) =
      stokesGammaCumulativeReadout v1 v2 (v1 • s1 + v2 • s2) := by
  simp [stokesCumulativeReadout, stokesCumulativePair,
    stokesGammaCumulativeReadout, Pi.add_apply, Pi.smul_apply]

theorem stokesCumulativeReadout_pair_eq_cubicPolarization
    (v1 v2 : ℂ) (s1 s2 : Fin 3 → ℂ) :
    stokesCumulativeReadout v1 v2 (stokesCumulativePair s1 s2) =
      cubicPolarization
        (stokesNormalReadout (stokesCumulativePair s1 s2)) v1 v2 := by
  exact stokesCumulativeReadout_eq_cubicPolarization
    v1 v2 (stokesCumulativePair s1 s2)

theorem stokesCumulativeReadout_fieldPair_eq_singleFieldReadout
    (v1 v2 : ℂ) (f1 f2 : ℝ → ℂ) (t1 t2 : ℝ) :
    stokesCumulativeReadout v1 v2
        (stokesCumulativeFieldPair f1 f2 t1 t2) =
      stokesGammaCumulativeReadout v1 v2
        (v1 • stokesCumulativeChannels f1 t1 t2 +
          v2 • stokesCumulativeChannels f2 t1 t2) := by
  exact stokesCumulativeReadout_pair_eq_gammaCumulativeReadout
    v1 v2 (stokesCumulativeChannels f1 t1 t2)
      (stokesCumulativeChannels f2 t1 t2)

theorem stokesCumulativeReadout_fieldPair_eq_mixedField
    (v1 v2 : ℂ) (f1 f2 : ℝ → ℂ) (t1 t2 : ℝ)
    (hf1 : Integrable f1) (hf2 : Integrable f2) :
    stokesCumulativeReadout v1 v2
        (stokesCumulativeFieldPair f1 f2 t1 t2) =
      stokesGammaCumulativeReadout v1 v2
        (stokesCumulativeChannels
          (fun x => v1 * f1 x + v2 * f2 x) t1 t2) := by
  rw [stokesCumulativeReadout_fieldPair_eq_singleFieldReadout]
  rw [stokesCumulativeChannels_linear f1 f2 v1 v2 t1 t2 hf1 hf2]

end
end NativeCarryFiveFieldCapstone

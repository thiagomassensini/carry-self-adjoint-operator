import CarrySelfAdjointOperator.FiveFieldStokesReadoutAlgebra

/-!
The six Stokes channels are cumulative evaluations of two scalar densities.
This file formalizes only the linearity of that construction under the
integrability hypotheses needed by the Bochner integral.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

open MeasureTheory

def stokesCumulativeChannels
    (f : ℝ → ℂ) (t1 t2 : ℝ) : Fin 3 → ℂ :=
  ![
    ∫ x in Set.Iic (0 : ℝ), f x,
    (∫ x in Set.Iic (0 : ℝ), f x) +
      (∫ x in Set.Ioc (0 : ℝ) t1, f x),
    (∫ x in Set.Iic (0 : ℝ), f x) +
      (∫ x in Set.Ioc (0 : ℝ) t1, f x) +
      (∫ x in Set.Ioc t1 t2, f x)
  ]

theorem stokesCumulativeChannels_linear
    (f1 f2 : ℝ → ℂ) (v1 v2 : ℂ) (t1 t2 : ℝ)
    (hf1 : Integrable f1) (hf2 : Integrable f2) :
    stokesCumulativeChannels (fun x => v1 * f1 x + v2 * f2 x) t1 t2 =
      v1 • stokesCumulativeChannels f1 t1 t2 +
        v2 • stokesCumulativeChannels f2 t1 t2 := by
  have hlin (s : Set ℝ) :
      (∫ x in s, v1 * f1 x + v2 * f2 x) =
        v1 * (∫ x in s, f1 x) + v2 * (∫ x in s, f2 x) := by
    rw [integral_add
      (hf1.integrableOn.integrable.const_mul v1)
      (hf2.integrableOn.integrable.const_mul v2)]
    rw [integral_const_mul, integral_const_mul]
  have h0 := hlin (Set.Iic (0 : ℝ))
  have h1 := hlin (Set.Ioc (0 : ℝ) t1)
  have h2 := hlin (Set.Ioc t1 t2)
  funext i
  fin_cases i
  · change (∫ x in Set.Iic (0 : ℝ), v1 * f1 x + v2 * f2 x) =
      v1 * (∫ x in Set.Iic (0 : ℝ), f1 x) +
        v2 * (∫ x in Set.Iic (0 : ℝ), f2 x)
    exact h0
  · change
      (∫ x in Set.Iic (0 : ℝ), v1 * f1 x + v2 * f2 x) +
          ∫ x in Set.Ioc (0 : ℝ) t1, v1 * f1 x + v2 * f2 x =
        v1 * ((∫ x in Set.Iic (0 : ℝ), f1 x) +
          ∫ x in Set.Ioc (0 : ℝ) t1, f1 x) +
        v2 * ((∫ x in Set.Iic (0 : ℝ), f2 x) +
          ∫ x in Set.Ioc (0 : ℝ) t1, f2 x)
    rw [h0, h1]
    ring
  · simp [stokesCumulativeChannels]
    rw [h0, h1, h2]
    ring

end
end NativeCarryFiveFieldCapstone

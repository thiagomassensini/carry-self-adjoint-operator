import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# C2 central and leg terms in one Cauchy Hilbert carrier

The finite identities below keep the original Hilbert inner product and all
ordered cross terms. The approximation estimate is unsigned: it does not
assume positivity of either the complete or truncated readout.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators ComplexConjugate

noncomputable section
set_option autoImplicit false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Finite synthesis in the given Hilbert carrier. -/
def c2CauchySynthesis {N : ℕ} (a : Fin N → ℂ) (φ : Fin N → H) : H :=
  ∑ i, a i • φ i

/-- The value channel `U = Σ aᵢ Fᵢ φᵢ`. -/
def c2CauchyValueSynthesis {N : ℕ} (a F : Fin N → ℂ)
    (φ : Fin N → H) : H :=
  c2CauchySynthesis (fun i => a i * F i) φ

/-- The central companion channel `T = Σ aᵢ C₀,ᵢ φᵢ`. -/
def c2CauchyCentralSynthesis {N : ℕ} (a C₀ : Fin N → ℂ)
    (φ : Fin N → H) : H :=
  c2CauchySynthesis (fun i => a i * C₀ i) φ

/-- The leg channel `P = Σ aᵢ Lᵢ Eᵢ φᵢ`. -/
def c2CauchyLegSynthesis {N : ℕ} (a L E : Fin N → ℂ)
    (φ : Fin N → H) : H :=
  c2CauchySynthesis (fun i => a i * L i * E i) φ

/-- Direct synthesis of a scalar companion family. -/
def c2CauchyCompanionSynthesis {N : ℕ} (a C : Fin N → ℂ)
    (φ : Fin N → H) : H :=
  c2CauchySynthesis (fun i => a i * C i) φ

/-- A pointwise `Cᵢ = C₀,ᵢ + i Lᵢ Eᵢ` identity transports through the same
finite synthesis, without changing its weights or feature vectors. -/
theorem c2CauchyCompanionSynthesis_eq_central_add_legs
    {N : ℕ} (a C C₀ L E : Fin N → ℂ) (φ : Fin N → H)
    (hC : ∀ i, C i = C₀ i + Complex.I * L i * E i) :
    c2CauchyCompanionSynthesis a C φ =
      c2CauchyCentralSynthesis a C₀ φ +
        Complex.I • c2CauchyLegSynthesis a L E φ := by
  simp only [c2CauchyCompanionSynthesis, c2CauchyCentralSynthesis,
    c2CauchyLegSynthesis, c2CauchySynthesis]
  calc
    (∑ i, (a i * C i) • φ i) =
        ∑ i, ((a i * C₀ i) • φ i +
          (Complex.I * (a i * L i * E i)) • φ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hC i, mul_add, add_smul]
      have hcoeff :
          a i * (Complex.I * L i * E i) =
            Complex.I * (a i * L i * E i) := by ring
      rw [hcoeff]
    _ = (∑ i, (a i * C₀ i) • φ i) +
        Complex.I • (∑ i, (a i * L i * E i) • φ i) := by
      simp only [Finset.sum_add_distrib, Finset.smul_sum, smul_smul]

/-- The C2 companion readout splits into its central and leg readouts. -/
theorem c2CauchyDefect_eq_central_add_legs
    (U T P : H) :
    -2 * (inner ℂ U (T + Complex.I • P)).im =
      -2 * (inner ℂ U T).im - 2 * (inner ℂ U P).re := by
  rw [inner_add_right, inner_smul_right, Complex.add_im, Complex.I_mul_im]
  ring

/-- Expand a pairing of two finite syntheses as a sum over every ordered pair
of input indices. No cross terms are dropped or symmetrized. -/
theorem c2CauchySynthesis_inner_eq_double_sum
    {N : ℕ} (a b : Fin N → ℂ) (φ ψ : Fin N → H) :
    inner ℂ (c2CauchySynthesis a φ) (c2CauchySynthesis b ψ) =
      ∑ i, ∑ j, b j * (star (a i) * inner ℂ (φ i) (ψ j)) := by
  simp only [c2CauchySynthesis, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [starRingEnd_apply]

/-- The value-central pairing retains every ordered pair `(i,j)`. -/
theorem c2CauchyValueCentral_inner_eq_double_sum
    {N : ℕ} (a F C₀ : Fin N → ℂ) (φ : Fin N → H) :
    inner ℂ (c2CauchyValueSynthesis a F φ)
      (c2CauchyCentralSynthesis a C₀ φ) =
      ∑ i, ∑ j, (a j * C₀ j) *
        (star (a i * F i) * inner ℂ (φ i) (φ j)) := by
  exact c2CauchySynthesis_inner_eq_double_sum
    (fun i => a i * F i) (fun i => a i * C₀ i) φ φ

/-- The value-leg pairing retains every ordered pair `(i,j)`. -/
theorem c2CauchyValueLeg_inner_eq_double_sum
    {N : ℕ} (a F L E : Fin N → ℂ) (φ : Fin N → H) :
    inner ℂ (c2CauchyValueSynthesis a F φ)
      (c2CauchyLegSynthesis a L E φ) =
      ∑ i, ∑ j, (a j * L j * E j) *
        (star (a i * F i) * inner ℂ (φ i) (φ j)) := by
  exact c2CauchySynthesis_inner_eq_double_sum
    (fun i => a i * F i) (fun i => a i * L i * E i) φ φ

/-- Signed readout associated with an ordered pair of carrier vectors. -/
def c2CarrierDefect (U C : H) : ℝ := -2 * (inner ℂ U C).im

/-- Expand the complete pairing around its two approximants. -/
theorem c2CarrierInner_approximation_expansion
    (Uₘ Cₘ δU δC : H) :
    inner ℂ (Uₘ + δU) (Cₘ + δC) =
      inner ℂ Uₘ Cₘ + inner ℂ Uₘ δC +
        inner ℂ δU Cₘ + inner ℂ δU δC := by
  simp only [inner_add_left, inner_add_right]
  ring

/-- Unsigned error estimate for replacing both vectors in the mixed readout.
It uses only the inner-product expansion and Cauchy--Schwarz. -/
theorem c2CarrierDefect_approximation_error_bound
    (U C Uₘ Cₘ : H) :
    |c2CarrierDefect U C - c2CarrierDefect Uₘ Cₘ| ≤
      2 * (‖U - Uₘ‖ * ‖Cₘ‖ + ‖Uₘ‖ * ‖C - Cₘ‖ +
        ‖U - Uₘ‖ * ‖C - Cₘ‖) := by
  let δU := U - Uₘ
  let δC := C - Cₘ
  have hU : U = Uₘ + δU := by simp [δU]
  have hC : C = Cₘ + δC := by simp [δC]
  have hdiff : c2CarrierDefect U C - c2CarrierDefect Uₘ Cₘ =
      -2 * ((inner ℂ Uₘ δC).im + (inner ℂ δU Cₘ).im +
        (inner ℂ δU δC).im) := by
    rw [hU, hC]
    simp only [c2CarrierDefect, inner_add_left, inner_add_right,
      Complex.add_im]
    ring
  have h₁ : |(inner ℂ Uₘ δC).im| ≤ ‖Uₘ‖ * ‖δC‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have h₂ : |(inner ℂ δU Cₘ).im| ≤ ‖δU‖ * ‖Cₘ‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have h₃ : |(inner ℂ δU δC).im| ≤ ‖δU‖ * ‖δC‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have hsum :
      |(inner ℂ Uₘ δC).im + (inner ℂ δU Cₘ).im +
          (inner ℂ δU δC).im| ≤
        |(inner ℂ Uₘ δC).im| + |(inner ℂ δU Cₘ).im| +
          |(inner ℂ δU δC).im| := by
    calc
      _ ≤ |(inner ℂ Uₘ δC).im + (inner ℂ δU Cₘ).im| +
          |(inner ℂ δU δC).im| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  rw [hdiff, abs_mul]
  norm_num
  dsimp [δU, δC] at h₁ h₂ h₃ hsum ⊢
  nlinarith

end
end CarrySelfAdjointOperator

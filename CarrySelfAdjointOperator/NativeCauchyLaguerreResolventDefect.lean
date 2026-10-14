import CarrySelfAdjointOperator.NativeCauchyLaguerreIsometry
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Quadratic Jacobi resolvents, parity Green states, and retained defects

The finite Jacobi study in `momentos` uses `X - z^2 J X = source`.
For an energy factor `J = B* B`, the corresponding Green state is the
two-sector vector `(X, z B X)`. Its Gram is the normalized height Pick
kernel only after retaining the two vector equation residuals below.

The second, independent defect is the division-free characteristic equation
`F' + 2 z q F`. Both are kept explicitly. Nothing in this file identifies
the physical source with the canonical moment Gram, asserts an infinite
tail estimate, or changes the original Cauchy metric.
-/

namespace CarrySelfAdjointOperator.HeightResolventGreenDefect

open Filter Topology
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

variable {H K H' K' : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
variable [NormedAddCommGroup K'] [InnerProductSpace ℂ K']

/-- Full vector residual, before any cyclic readout. -/
def quadraticResidual (J : H →L[ℂ] H) (source : H) (z : ℂ) (x : H) : H :=
  x - z ^ 2 • J x - source

/-- The even response and the height-weighted odd energy response. -/
def parityState (B : H →L[ℂ] K) (z : ℂ) (x : H) : WithLp 2 (H × K) :=
  WithLp.toLp 2 (x, z • B x)

/-- The full parity Gram; no output sector is projected away. -/
def parityGram (B : H →L[ℂ] K) (z w : ℂ) (x y : H) : ℂ :=
  inner ℂ x y + conj z * w * inner ℂ (B x) (B y)

theorem parityGram_eq_inner (B : H →L[ℂ] K) (z w : ℂ) (x y : H) :
    parityGram B z w x y = inner ℂ (parityState B z x) (parityState B w y) := by
  change inner ℂ x y + conj z * w * inner ℂ (B x) (B y) =
    inner ℂ x y + inner ℂ (z • B x) (w • B y)
  rw [inner_smul_left, inner_smul_right]
  ring

/-- Half of the height logarithmic-derivative Pick kernel, with the
cyclic readout still tied to the source of the vector equation. -/
def readoutKernel (source : H) (z w : ℂ) (x y : H) : ℂ :=
  (w * inner ℂ source y - conj (z * inner ℂ source x)) / (w - conj z)

/-- The two ordered cross terms of the vector equation residuals. -/
def vectorDefectNumerator (J : H →L[ℂ] H) (source : H)
    (z w : ℂ) (x y : H) : ℂ :=
  conj z * inner ℂ x (quadraticResidual J source w y) -
    w * inner ℂ (quadraticResidual J source z x) y

/-- Exact division-free identity. The energy equality is explicit and
does not assume the canonical native moment Gram. -/
theorem weightedReadout_sub_parityGram
    (J : H →L[ℂ] H) (B : H →L[ℂ] K)
    (henergy : ∀ x y : H, inner ℂ (J x) y = inner ℂ (B x) (B y))
    (source : H) (z w : ℂ) (x y : H) :
    w * inner ℂ source y - conj (z * inner ℂ source x) -
        (w - conj z) * parityGram B z w x y =
      vectorDefectNumerator J source z w x y := by
  have hright : inner ℂ x (J y) = inner ℂ (B x) (B y) := by
    calc
      inner ℂ x (J y) = conj (inner ℂ (J y) x) := (inner_conj_symm x (J y)).symm
      _ = conj (inner ℂ (B y) (B x)) := by rw [henergy]
      _ = inner ℂ (B x) (B y) := inner_conj_symm (B x) (B y)
  simp only [vectorDefectNumerator, quadraticResidual, parityGram,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    map_mul, map_pow, inner_conj_symm, henergy, hright]
  ring

/-- The normalized scalar kernel equals the two-sector Gram plus the
same vector residual cross terms. -/
theorem readoutKernel_sub_parityGram
    (J : H →L[ℂ] H) (B : H →L[ℂ] K)
    (henergy : ∀ x y : H, inner ℂ (J x) y = inner ℂ (B x) (B y))
    (source : H) (z w : ℂ) (x y : H) (hsep : w ≠ conj z) :
    readoutKernel source z w x y - parityGram B z w x y =
      vectorDefectNumerator J source z w x y / (w - conj z) := by
  have h := weightedReadout_sub_parityGram J B henergy source z w x y
  unfold readoutKernel
  field_simp [sub_ne_zero.mpr hsep]
  linear_combination h

/-- Exact responses realize the normalized Green kernel as a Gram. -/
theorem readoutKernel_eq_parityState_inner
    (J : H →L[ℂ] H) (B : H →L[ℂ] K)
    (henergy : ∀ x y : H, inner ℂ (J x) y = inner ℂ (B x) (B y))
    (source : H) (z w : ℂ) (x y : H) (hsep : w ≠ conj z)
    (hx : x - z ^ 2 • J x = source)
    (hy : y - w ^ 2 • J y = source) :
    readoutKernel source z w x y =
      inner ℂ (parityState B z x) (parityState B w y) := by
  have h := readoutKernel_sub_parityGram J B henergy source z w x y hsep
  simp only [vectorDefectNumerator, quadraticResidual, hx, hy,
    sub_self, inner_zero_right, inner_zero_left, mul_zero,
    zero_div] at h
  rw [sub_eq_zero, parityGram_eq_inner] at h
  exact h

/-- An a posteriori kernel bound needs vector residual norms, including
their mixed crossings, rather than only one scalar residual. -/
theorem norm_readoutKernel_sub_parityGram_le
    (J : H →L[ℂ] H) (B : H →L[ℂ] K)
    (henergy : ∀ x y : H, inner ℂ (J x) y = inner ℂ (B x) (B y))
    (source : H) (z w : ℂ) (x y : H) (hsep : w ≠ conj z) :
    ‖readoutKernel source z w x y - parityGram B z w x y‖ ≤
      (‖z‖ * ‖x‖ * ‖quadraticResidual J source w y‖ +
        ‖w‖ * ‖quadraticResidual J source z x‖ * ‖y‖) / ‖w - conj z‖ := by
  rw [readoutKernel_sub_parityGram J B henergy source z w x y hsep, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  unfold vectorDefectNumerator
  calc
    _ ≤ ‖conj z * inner ℂ x (quadraticResidual J source w y)‖ +
        ‖w * inner ℂ (quadraticResidual J source z x) y‖ := norm_sub_le _ _
    _ ≤ _ := by
      simp only [norm_mul, Complex.norm_conj]
      have h₁ := norm_inner_le_norm (𝕜 := ℂ) x (quadraticResidual J source w y)
      have h₂ := norm_inner_le_norm (𝕜 := ℂ) (quadraticResidual J source z x) y
      nlinarith [mul_le_mul_of_nonneg_left h₁ (norm_nonneg z),
        mul_le_mul_of_nonneg_left h₂ (norm_nonneg w)]

/-- Division-free residual for the original characteristic and its derivative. -/
def characteristicResidual (F D z q : ℂ) : ℂ := D + 2 * z * q * F

/-- Native normalized Wronskian kernel, with the fixed factor one half. -/
def characteristicKernel (Fz Fw Dz Dw z w : ℂ) : ℂ :=
  ((-Dw / Fw) - conj (-Dz / Fz)) / (2 * (w - conj z))

/-- Exact separation of characteristic mismatch from the finite cyclic
readout. No equality with the native characteristic is inserted as a premise. -/
theorem characteristicKernel_sub_readoutKernel
    (source : H) (z w : ℂ) (x y : H) (Fz Fw Dz Dw : ℂ)
    (hzF : Fz ≠ 0) (hwF : Fw ≠ 0) (hsep : w ≠ conj z) :
    characteristicKernel Fz Fw Dz Dw z w - readoutKernel source z w x y =
      (-characteristicResidual Fw Dw w (inner ℂ source y) / Fw +
        conj (characteristicResidual Fz Dz z (inner ℂ source x) / Fz)) /
          (2 * (w - conj z)) := by
  simp only [characteristicKernel, characteristicResidual, readoutKernel,
    map_div₀, map_add, map_mul, map_neg, map_ofNat]
  have hzconj : conj Fz ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hzF
  field_simp [hzF, hwF, hzconj, sub_ne_zero.mpr hsep]
  ring

/-- The native-versus-Gram defect has two separate, explicit sources:
the vector equation and the original characteristic equation. -/
theorem characteristicKernel_sub_parityGram
    (J : H →L[ℂ] H) (B : H →L[ℂ] K)
    (henergy : ∀ x y : H, inner ℂ (J x) y = inner ℂ (B x) (B y))
    (source : H) (z w : ℂ) (x y : H) (Fz Fw Dz Dw : ℂ)
    (hzF : Fz ≠ 0) (hwF : Fw ≠ 0) (hsep : w ≠ conj z) :
    characteristicKernel Fz Fw Dz Dw z w - parityGram B z w x y =
      vectorDefectNumerator J source z w x y / (w - conj z) +
        (-characteristicResidual Fw Dw w (inner ℂ source y) / Fw +
          conj (characteristicResidual Fz Dz z (inner ℂ source x) / Fz)) /
            (2 * (w - conj z)) := by
  have h₁ := readoutKernel_sub_parityGram J B henergy source z w x y hsep
  have h₂ := characteristicKernel_sub_readoutKernel source z w x y Fz Fw Dz Dw
    hzF hwF hsep
  linear_combination h₁ + h₂

/-- Quantitative separation of both defects. The factors `Fz`, `Fw` and
`w - conj z` stay visible; no uniform estimate near a pole is claimed. -/
theorem norm_characteristicKernel_sub_parityGram_le
    (J : H →L[ℂ] H) (B : H →L[ℂ] K)
    (henergy : ∀ x y : H, inner ℂ (J x) y = inner ℂ (B x) (B y))
    (source : H) (z w : ℂ) (x y : H) (Fz Fw Dz Dw : ℂ)
    (hzF : Fz ≠ 0) (hwF : Fw ≠ 0) (hsep : w ≠ conj z) :
    ‖characteristicKernel Fz Fw Dz Dw z w - parityGram B z w x y‖ ≤
      (‖z‖ * ‖x‖ * ‖quadraticResidual J source w y‖ +
        ‖w‖ * ‖quadraticResidual J source z x‖ * ‖y‖) / ‖w - conj z‖ +
      (‖characteristicResidual Fw Dw w (inner ℂ source y)‖ / ‖Fw‖ +
        ‖characteristicResidual Fz Dz z (inner ℂ source x)‖ / ‖Fz‖) /
          (2 * ‖w - conj z‖) := by
  have hchar :
      ‖characteristicKernel Fz Fw Dz Dw z w - readoutKernel source z w x y‖ ≤
        (‖characteristicResidual Fw Dw w (inner ℂ source y)‖ / ‖Fw‖ +
          ‖characteristicResidual Fz Dz z (inner ℂ source x)‖ / ‖Fz‖) /
            (2 * ‖w - conj z‖) := by
    rw [characteristicKernel_sub_readoutKernel source z w x y Fz Fw Dz Dw
      hzF hwF hsep, norm_div]
    calc
      _ ≤ (‖-characteristicResidual Fw Dw w (inner ℂ source y) / Fw‖ +
          ‖conj (characteristicResidual Fz Dz z (inner ℂ source x) / Fz)‖) /
            ‖(2 : ℂ) * (w - conj z)‖ :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
      _ = _ := by simp only [norm_div, norm_neg, Complex.norm_conj, norm_mul]; norm_num
  calc
    _ = ‖(readoutKernel source z w x y - parityGram B z w x y) +
        (characteristicKernel Fz Fw Dz Dw z w - readoutKernel source z w x y)‖ := by
      congr 1
      ring
    _ ≤ ‖readoutKernel source z w x y - parityGram B z w x y‖ +
        ‖characteristicKernel Fz Fw Dz Dw z w - readoutKernel source z w x y‖ :=
      norm_add_le _ _
    _ ≤ _ := add_le_add
      (norm_readoutKernel_sub_parityGram_le J B henergy source z w x y hsep) hchar

/-- A source-specific limit criterion. No operator-norm convergence of the
Jacobi tower is required: both response sectors and the two explicit
residuals must converge in the common Hilbert spaces. -/
theorem characteristicKernel_eq_limit_parityGram
    (J : ℕ → H →L[ℂ] H) (B : ℕ → H →L[ℂ] K)
    (henergy : ∀ n x y, inner ℂ (J n x) y = inner ℂ (B n x) (B n y))
    (source : H) (z w : ℂ) (X Y : ℕ → H) (x y : H) (bx by' : K)
    (Fz Fw Dz Dw : ℂ) (hzF : Fz ≠ 0) (hwF : Fw ≠ 0) (hsep : w ≠ conj z)
    (hX : Tendsto X atTop (nhds x)) (hY : Tendsto Y atTop (nhds y))
    (hBX : Tendsto (fun n ↦ B n (X n)) atTop (nhds bx))
    (hBY : Tendsto (fun n ↦ B n (Y n)) atTop (nhds by'))
    (hRz : Tendsto (fun n ↦ quadraticResidual (J n) source z (X n)) atTop (nhds 0))
    (hRw : Tendsto (fun n ↦ quadraticResidual (J n) source w (Y n)) atTop (nhds 0))
    (hDz : Tendsto (fun n ↦ characteristicResidual Fz Dz z (inner ℂ source (X n)))
      atTop (nhds 0))
    (hDw : Tendsto (fun n ↦ characteristicResidual Fw Dw w (inner ℂ source (Y n)))
      atTop (nhds 0)) :
    characteristicKernel Fz Fw Dz Dw z w =
      inner ℂ x y + conj z * w * inner ℂ bx by' := by
  have hgram : Tendsto (fun n ↦ parityGram (B n) z w (X n) (Y n)) atTop
      (nhds (inner ℂ x y + conj z * w * inner ℂ bx by')) :=
    (hX.inner hY).add (tendsto_const_nhds.mul (hBX.inner hBY))
  have hvec : Tendsto (fun n ↦ vectorDefectNumerator (J n) source z w (X n) (Y n))
      atTop (nhds 0) := by
    simpa only [vectorDefectNumerator, inner_zero_right, inner_zero_left, mul_zero,
      sub_zero] using
        ((tendsto_const_nhds (x := conj z)).mul (hX.inner (𝕜 := ℂ) hRw)).sub
          ((tendsto_const_nhds (x := w)).mul (hRz.inner (𝕜 := ℂ) hY))
  have hchar : Tendsto (fun n ↦
      (-characteristicResidual Fw Dw w (inner ℂ source (Y n)) / Fw +
        conj (characteristicResidual Fz Dz z (inner ℂ source (X n)) / Fz)) /
          (2 * (w - conj z))) atTop (nhds 0) := by
    simpa only [neg_zero, zero_div, map_zero, add_zero, Function.comp_apply] using
      ((hDw.neg.div_const Fw).add
        (Complex.continuous_conj.tendsto (0 / Fz) |>.comp (hDz.div_const Fz))).div_const
          (2 * (w - conj z))
  have hlimit := (hgram.add (hvec.div_const (w - conj z))).add hchar
  simp only [zero_div, add_zero] at hlimit
  have heq : ∀ n,
      parityGram (B n) z w (X n) (Y n) +
          vectorDefectNumerator (J n) source z w (X n) (Y n) / (w - conj z) +
          (-characteristicResidual Fw Dw w (inner ℂ source (Y n)) / Fw +
            conj (characteristicResidual Fz Dz z (inner ℂ source (X n)) / Fz)) /
              (2 * (w - conj z)) = characteristicKernel Fz Fw Dz Dw z w := by
    intro n
    have h := characteristicKernel_sub_parityGram (J n) (B n) (henergy n)
      source z w (X n) (Y n) Fz Fw Dz Dw hzF hwF hsep
    linear_combination -h
  simp only [heq] at hlimit
  exact tendsto_nhds_unique tendsto_const_nhds hlimit

/-- An isometry preserves the full vector equation residual, even before
an operator on the target has been defined. -/
theorem isometry_map_graph_residual (U : H →ₗᵢ[ℂ] H')
    (source x jx : H) (z : ℂ) :
    U (x - z ^ 2 • jx - source) = U x - z ^ 2 • U jx - U source := by
  simp only [map_sub, map_smul]

theorem isometry_graph_residual_norm (U : H →ₗᵢ[ℂ] H')
    (source x jx : H) (z : ℂ) :
    ‖U x - z ^ 2 • U jx - U source‖ = ‖x - z ^ 2 • jx - source‖ := by
  rw [← isometry_map_graph_residual, U.norm_map]

/-- Both parity sectors, including their complex height weights, retain
the same Gram under independent isometric coordinate maps. -/
theorem isometry_parity_gram (U : H →ₗᵢ[ℂ] H') (V : K →ₗᵢ[ℂ] K')
    (x y : H) (bx by' : K) (z w : ℂ) :
    inner ℂ (U x) (U y) + conj z * w * inner ℂ (V bx) (V by') =
      inner ℂ x y + conj z * w * inner ℂ bx by' := by
  rw [U.inner_map_map, V.inner_map_map]

end
end CarrySelfAdjointOperator.HeightResolventGreenDefect

namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped InnerProductSpace ComplexConjugate lp
noncomputable section

/-- The literal physical Cauchy dictionary preserves the graph residual
norm. No height operator on its target is assumed or defined here. -/
theorem cauchyLaguerre_graph_residual_norm
    (source x jx : PhysicalCauchySpace) (z : ℂ) :
    ‖cauchyLaguerreIsometry x - z ^ 2 • cauchyLaguerreIsometry jx -
        cauchyLaguerreIsometry source‖ = ‖x - z ^ 2 • jx - source‖ :=
  HeightResolventGreenDefect.isometry_graph_residual_norm
    cauchyLaguerreIsometry source x jx z

/-- The original two physical sectors retain their full parity Gram. -/
theorem cauchyLaguerre_parity_resolvent_gram
    (x y bx by' : PhysicalCauchySpace) (z w : ℂ) :
    inner ℂ (cauchyLaguerreIsometry x) (cauchyLaguerreIsometry y) +
        conj z * w * inner ℂ (cauchyLaguerreIsometry bx) (cauchyLaguerreIsometry by') =
      inner ℂ x y + conj z * w * inner ℂ bx by' :=
  HeightResolventGreenDefect.isometry_parity_gram
    cauchyLaguerreIsometry cauchyLaguerreIsometry x y bx by' z w

end
end CarrySelfAdjointOperator.NativeLaguerre

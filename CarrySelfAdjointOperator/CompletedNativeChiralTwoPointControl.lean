import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralCarrier
import CarrySelfAdjointOperator.CompletedNativeXiCosineMomentHerglotzGate
import CarrySelfAdjointOperator.C3DynamicCompletedGreenForm
import Mathlib.Analysis.Matrix.PosDef

/-!
# Explicit two-point control in the existing completed chiral realization

The determinant of the existing radial Pick matrix measures the variation
of the completed chiral quotient, including its off-diagonal term. Certified
theta bounds already prove eventual positivity of this two-point matrix.
We expose that consequence as a quotient inequality, a synthesis estimate,
and a division-free estimate on the complete `(F,-F')` trace.
No assertion about arbitrary matrix size follows from this two-point result.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace CarrySelfAdjointOperator

open Filter

noncomputable section
set_option autoImplicit false

/-- The cross term cannot be recovered from the two diagonal defects alone. -/
theorem chiralTwoPoint_cross_normSq (q₀ q₁ : ℂ) :
    Complex.normSq (1 - conj q₀ * q₁) =
      (1 - Complex.normSq q₀) * (1 - Complex.normSq q₁) +
        Complex.normSq (q₁ - q₀) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Exact determinant of the existing two-point matrix, with the radial
scale retained. The coefficient eight comes from its `2,3,4` denominators. -/
theorem canonicalCompletedNativeRadialChiralPickSampleMatrix_two_det (k : ℕ) :
    let q₀ := completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k 0)
    let q₁ := completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k 1)
    (canonicalCompletedNativeRadialChiralPickSampleMatrix k 2).det =
      (((k : ℝ) + 1)^2 / 72 *
        ((1 - Complex.normSq q₀) * (1 - Complex.normSq q₁) -
          8 * Complex.normSq (q₁ - q₀)) : ℝ) := by
  dsimp only
  rw [canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect,
    Matrix.det_fin_two]
  simp only [canonicalCompletedNativeRadialChiralMultiplierDefectMatrix_apply]
  norm_num
  apply Complex.ext <;>
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      pow_two, Complex.add_re, Complex.add_im] <;> ring

/-- Exact nonnegative-determinant criterion; diagonal signs remain separate. -/
theorem canonicalCompletedNativeRadialChiralPickSampleMatrix_two_det_nonneg_iff
    (k : ℕ) :
    0 ≤ (canonicalCompletedNativeRadialChiralPickSampleMatrix k 2).det ↔
      8 * Complex.normSq
        (completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k 1) -
          completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k 0)) ≤
        (1 - Complex.normSq (completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k 0))) *
        (1 - Complex.normSq (completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k 1))) := by
  rw [canonicalCompletedNativeRadialChiralPickSampleMatrix_two_det]
  rw [Complex.zero_le_real]
  have hs : 0 < ((k : ℝ) + 1)^2 / 72 := by positivity
  rw [mul_nonneg_iff_of_pos_left hs, sub_nonneg]

/-- The proposed polarized inequality is already a consequence of the
certified low-order theta moments, for sufficiently small radial steps. -/
theorem canonicalCompletedNativeChiralTwoPoint_variation_eventually :
    ∀ᶠ k : ℕ in atTop,
      8 * Complex.normSq
        (completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k 1) -
          completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k 0)) ≤
        (1 - Complex.normSq (completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k 0))) *
        (1 - Complex.normSq (completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k 1))) := by
  filter_upwards
    [canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef]
    with k hk
  exact (canonicalCompletedNativeRadialChiralPickSampleMatrix_two_det_nonneg_iff k).mp
    hk.det_nonneg

/-- Both pointwise defects have the required sign on the same eventual
two-point family. These signs alone do not imply the preceding estimate. -/
theorem canonicalCompletedNativeChiralTwoPoint_diagonals_eventually :
    ∀ᶠ k : ℕ in atTop, ∀ i : Fin 2,
      Complex.normSq (completedNativeHermiteBiehlerChiralQuotient
        (canonicalCompletedC3RadialTiltPoint k i)) ≤ 1 := by
  filter_upwards
    [canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef]
    with k hk i
  have hd := hk.diag_nonneg (i := i)
  rw [canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect,
    canonicalCompletedNativeRadialChiralMultiplierDefectMatrix_apply] at hd
  have hr := (RCLike.le_iff_re_im.mp hd).1
  simp only [RCLike.re_to_complex, map_zero, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.sub_re, Complex.one_re] at hr
  have he : (conj (completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k i)) *
      completedNativeHermiteBiehlerChiralQuotient
        (canonicalCompletedC3RadialTiltPoint k i)).re =
      Complex.normSq (completedNativeHermiteBiehlerChiralQuotient
        (canonicalCompletedC3RadialTiltPoint k i)) := by
    simp [Complex.normSq_apply, Complex.mul_re]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at he hr
  rw [he] at hr
  have hs : 0 < ((k : ℝ) + 1) * (((i : ℕ) + (i : ℕ) + 2 : ℕ) : ℝ)⁻¹ := by
    positivity
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hs).mp hr)

/-- All complex linear combinations of these two Cauchy vectors satisfy
the chiral contraction estimate; this is not merely a diagonal comparison. -/
theorem canonicalCompletedNativeChiralTwoPoint_contractive_eventually :
    ∀ᶠ k : ℕ in atTop,
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k 2 := by
  filter_upwards
    [canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef]
    with k hk
  exact (canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
    k 2).mpr hk

/-- Preserve the exact amplitude already present in the signed native
realization, in every complex linear combination of the two states. -/
theorem canonicalCompletedNativeChiralTwoPoint_projective_energy_eventually :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin 2 → ℂ,
      ‖∑ i, c i • (canonicalCompletedNativeRadialProjectiveChiralState k i).2‖ ^ 2 ≤
        ‖∑ i, c i • (canonicalCompletedNativeRadialProjectiveChiralState k i).1‖ ^ 2 := by
  filter_upwards [canonicalCompletedNativeChiralTwoPoint_contractive_eventually]
    with k hk c
  have h := hk (fun i => c i * completedNativeNormalizedPositiveChiralAmplitude
    (canonicalCompletedC3RadialTiltPoint k i))
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  simpa only [canonicalCompletedNativeRadialProjectiveChiralState,
    canonicalCompletedNativeRadialChiralDefectState,
    Prod.smul_fst, Prod.smul_snd, smul_smul] using h

/-- The same two-point signed form is the native dslope and is eventually
positive. Its existing scalar identification is reused unchanged. -/
theorem canonicalCompletedNativeChiralTwoPoint_native_posSemidef_eventually :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialDslopeSampleMatrix k 2).PosSemidef := by
  filter_upwards
    [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 2,
      canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef]
    with k hreg hk
  exact (canonicalCompletedNativeRadialDslopeSampleMatrix_posSemidef_iff_pick
    k 2 hreg).mpr hk

/-- The determinant margin expressed as a polynomial of two full traces
`(F,C)`, where the completed companion is `C=-F'`. This is a diagnostic
scalar, not a new candidate kernel or a replacement boundary form. -/
def chiralTwoPointTraceMargin (r₀ r₁ : ℂ × ℂ) : ℝ :=
  (r₀.2 * conj r₀.1).im * (r₁.2 * conj r₁.1).im -
    2 * Complex.normSq (r₁.2 * r₀.1 - r₀.2 * r₁.1)

/-- Numerator of the quotient difference, before dividing by either
positive chiral coordinate. No division by `F` is needed. -/
theorem chiralTwoPoint_trace_cross (F₀ C₀ F₁ C₁ : ℂ) :
    (C₁ - Complex.I * F₁) * (C₀ + Complex.I * F₀) -
      (C₀ - Complex.I * F₀) * (C₁ + Complex.I * F₁) =
        2 * Complex.I * (C₁ * F₀ - C₀ * F₁) := by ring

/-- The oriented trace energy, with the sign fixed by `C+iF`. -/
theorem chiralTwoPoint_trace_diagonal (F C : ℂ) :
    Complex.normSq (C + Complex.I * F) -
      Complex.normSq (C - Complex.I * F) = 4 * (C * conj F).im := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The quotient determinant numerator is sixteen times the complete
trace margin. All cross terms and the quarter-turn are retained. -/
theorem chiralTwoPoint_trace_margin_numerator (F₀ C₀ F₁ C₁ : ℂ) :
    (Complex.normSq (C₀ + Complex.I * F₀) - Complex.normSq (C₀ - Complex.I * F₀)) *
      (Complex.normSq (C₁ + Complex.I * F₁) - Complex.normSq (C₁ - Complex.I * F₁)) -
      8 * Complex.normSq
        ((C₁ - Complex.I * F₁) * (C₀ + Complex.I * F₀) -
          (C₀ - Complex.I * F₀) * (C₁ + Complex.I * F₁)) =
      16 * chiralTwoPointTraceMargin (F₀,C₀) (F₁,C₁) := by
  rw [chiralTwoPoint_trace_cross, chiralTwoPoint_trace_diagonal,
    chiralTwoPoint_trace_diagonal]
  simp [chiralTwoPointTraceMargin, Complex.normSq_mul]
  ring

/-- Clearing only the two chiral denominators gives an exact polynomial
identity, so the variation bound has a division-free boundary formulation. -/
theorem chiralTwoPoint_quotient_margin (N₀ P₀ N₁ P₁ : ℂ)
    (hP₀ : P₀ ≠ 0) (hP₁ : P₁ ≠ 0) :
    ((1 - Complex.normSq (N₀/P₀)) * (1 - Complex.normSq (N₁/P₁)) -
      8 * Complex.normSq (N₁/P₁-N₀/P₀)) *
        (Complex.normSq P₀ * Complex.normSq P₁) =
      (Complex.normSq P₀ - Complex.normSq N₀) *
        (Complex.normSq P₁ - Complex.normSq N₁) -
      8 * Complex.normSq (N₁*P₀-N₀*P₁) := by
  rw [div_sub_div _ _ hP₁ hP₀]
  simp only [Complex.normSq_div, Complex.normSq_mul]
  field_simp [mt Complex.normSq_eq_zero.mp hP₀, mt Complex.normSq_eq_zero.mp hP₁]

/-- Exact equivalence between the proposed quotient estimate and a
nonnegative full-trace margin; neither native moment positivity nor a
Herglotz property is used as a premise. -/
theorem chiralTwoPoint_variation_iff_trace_margin (F₀ C₀ F₁ C₁ : ℂ)
    (hP₀ : C₀ + Complex.I * F₀ ≠ 0) (hP₁ : C₁ + Complex.I * F₁ ≠ 0) :
    8 * Complex.normSq
      ((C₁-Complex.I*F₁)/(C₁+Complex.I*F₁) -
        (C₀-Complex.I*F₀)/(C₀+Complex.I*F₀)) ≤
      (1-Complex.normSq ((C₀-Complex.I*F₀)/(C₀+Complex.I*F₀))) *
        (1-Complex.normSq ((C₁-Complex.I*F₁)/(C₁+Complex.I*F₁))) ↔
      0 ≤ chiralTwoPointTraceMargin (F₀,C₀) (F₁,C₁) := by
  have h := chiralTwoPoint_quotient_margin
    (C₀-Complex.I*F₀) (C₀+Complex.I*F₀)
    (C₁-Complex.I*F₁) (C₁+Complex.I*F₁) hP₀ hP₁
  rw [chiralTwoPoint_trace_margin_numerator] at h
  have hp : 0 < Complex.normSq (C₀+Complex.I*F₀) *
      Complex.normSq (C₁+Complex.I*F₁) :=
    mul_pos (Complex.normSq_pos.mpr hP₀) (Complex.normSq_pos.mpr hP₁)
  rw [← sub_nonneg, ← mul_nonneg_iff_of_pos_right hp, h]
  exact mul_nonneg_iff_of_pos_left (by norm_num : (0:ℝ) < 16)

/-- Specialize the algebraic criterion to the actual completed native
coordinates, retaining the existing boundary companion. -/
theorem completedNativeChiralTwoPoint_variation_iff_trace_margin
    (z w : ℂ)
    (hz : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0)
    (hw : completedNativePositiveHermiteBiehlerCoordinate w ≠ 0) :
    8 * Complex.normSq (completedNativeHermiteBiehlerChiralQuotient w -
      completedNativeHermiteBiehlerChiralQuotient z) ≤
      (1 - Complex.normSq (completedNativeHermiteBiehlerChiralQuotient z)) *
        (1 - Complex.normSq (completedNativeHermiteBiehlerChiralQuotient w)) ↔
      0 ≤ chiralTwoPointTraceMargin
        (completedNativeOperatorCharacteristic z, completedNativeOperatorBoundaryCompanion z)
        (completedNativeOperatorCharacteristic w, completedNativeOperatorBoundaryCompanion w) := by
  simpa only [completedNativeHermiteBiehlerChiralQuotient,
    completedNativePositiveHermiteBiehlerCoordinate,
    completedNativeNegativeHermiteBiehlerCoordinate,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv] using
      chiralTwoPoint_variation_iff_trace_margin
        (completedNativeOperatorCharacteristic z) (-deriv completedNativeOperatorCharacteristic z)
        (completedNativeOperatorCharacteristic w) (-deriv completedNativeOperatorCharacteristic w)
        hz hw

/-- An unconditional, division-free boundary estimate on the two radial
points. Its analytic input is the already certified theta moment bound. -/
theorem canonicalCompletedNativeChiralTwoPoint_trace_margin_eventually :
    ∀ᶠ k : ℕ in atTop,
      0 ≤ chiralTwoPointTraceMargin
        (completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0),
          completedNativeOperatorBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k 0))
        (completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1),
          completedNativeOperatorBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k 1)) := by
  filter_upwards [canonicalCompletedNativeChiralTwoPoint_variation_eventually,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 2] with k hk hreg
  exact (completedNativeChiralTwoPoint_variation_iff_trace_margin _ _
    (hreg 0).2.2 (hreg 1).2.2).mp hk

open CPFormal.Analytic.Cp NativeCarryC3Crosswalk

/-- Evaluate the existing completed trace pair using the seeded all-block
clock. Both tails, the chart derivative, and the completion companion remain
in the expression. This introduces no new state or operator. -/
theorem nativeC3Dynamic_completedTracePair_eq (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    let s := operatorHeightParameter z
    let state := canonicalCompletedC3HilbertPrefixState s (3*M)
    let r : ℂ × ℂ :=
      (1 + c3ReturnVarianceHeadReadout M s state.1 + realCpBracketCutoffTail 3 M s,
        nativeC3DynamicLogHead M s + canonicalC3LogJetCutoffTail M s)
    canonicalC3BracketTfvdCompletedTracePair M z =
      (nativeXiCompletionFactor z * (r.1 / cpChartFactor 3 s),
        nativeXiCompletionBoundaryCompanion z * (r.1 / cpChartFactor 3 s) +
          nativeXiCompletionFactor z *
            (Complex.I * ((r.2 * cpChartFactor 3 s +
              r.1 * deriv (cpChartFactor 3) s) / cpChartFactor 3 s ^ 2))) := by
  dsimp only
  rw [nativeC3DynamicLogHead_eq_returnVariance,
    c3ReturnVariance_dressedTrace_eq_F_negFprime M hz]
  exact canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M hz

/-- The two-point margin computed from the completed dynamic readouts is
cutoff independent, even when the two heads have different lengths. -/
theorem nativeC3Dynamic_chiralTwoPointTraceMargin_eq (M N : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    chiralTwoPointTraceMargin
      (canonicalC3BracketTfvdCompletedTracePair M z)
      (canonicalC3BracketTfvdCompletedTracePair N w) =
      chiralTwoPointTraceMargin
        (completedNativeOperatorCharacteristic z, completedNativeOperatorBoundaryCompanion z)
        (completedNativeOperatorCharacteristic w, completedNativeOperatorBoundaryCompanion w) := by
  rw [canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M hz,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime N hw,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv]

/-- Main completed-dynamics endpoint: one sufficiently small radial step
works for every pair of head cutoffs. Positivity comes from the existing
theta certificate; the clock/readout identities transport the exact trace.
This neither assumes nor establishes the all-order chiral multiplier gate. -/
theorem nativeC3Dynamic_chiralTwoPointTraceMargin_allCutoff_eventually :
    ∀ᶠ k : ℕ in atTop, ∀ M N : ℕ,
      0 ≤ chiralTwoPointTraceMargin
        (canonicalC3BracketTfvdCompletedTracePair M (canonicalCompletedC3RadialTiltPoint k 0))
        (canonicalC3BracketTfvdCompletedTracePair N (canonicalCompletedC3RadialTiltPoint k 1)) := by
  filter_upwards [canonicalCompletedNativeChiralTwoPoint_trace_margin_eventually,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 2]
    with k hk hreg M N
  rw [nativeC3Dynamic_chiralTwoPointTraceMargin_eq M N
    (z := canonicalCompletedC3RadialTiltPoint k 0)
    (w := canonicalCompletedC3RadialTiltPoint k 1) (hreg 0).1 (hreg 1).1]
  exact hk

/-- A finite algebraic witness: positive diagonal trace energies alone do
not control the crossing. These are arbitrary traces, not canonical native
points and not a counterexample to the preceding eventual theorem. -/
theorem chiralTwoPoint_diagonals_do_not_control_cross :
    0 < (Complex.I * conj (1 : ℂ)).im ∧
    0 < ((3 * Complex.I) * conj (1 : ℂ)).im ∧
    chiralTwoPointTraceMargin (1, Complex.I) (1, 3*Complex.I) = -5 := by
  norm_num [chiralTwoPointTraceMargin, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

end
end CarrySelfAdjointOperator

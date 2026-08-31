import CPFormal.Analytic.CpNativeGpreTowerLift
import CPFormal.Analytic.CpFiniteTfvdLogJetGreenComparison
import CPFormal.Analytic.CpGenuineFirstOrthogonalGreenLimit
import CPFormal.Analytic.CpTfvdSameEdgeReflectedEnergyCollapse
import CarrySelfAdjointOperator.CompletedC3RawGreenGamma
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Exact four-corner C3 Green cell

This module records the complete four-corner cell obtained by expanding the
product of the two adjacent discrete differences before reducing the rational
target.  The cell kills constants and affine functions around `1 / 2`, while
its quadratic centered moment is nonzero.  In logarithmic coordinates the
first moment survives as the exact Euler boundary coefficient.

No limit, positivity, characteristic zero, or spectral hypothesis is used.
-/

open scoped ComplexOrder InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The upper off-diagonal corner of the complete Green cell. -/
def canonicalC3FourCornerUpperPoint (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) / (2 * (n : ℝ))

/-- The lower off-diagonal corner of the complete Green cell. -/
def canonicalC3FourCornerLowerPoint (n : ℕ) : ℝ :=
  (n : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))

/--
The complete four-corner Green molecule, after removing its common external
weight.  Both diagonal corners lie at `1 / 2`; they remain separate in the
definition so the provenance of all four entries is retained.
-/
def canonicalC3FourCornerGreenCell (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  (1 / (n : ℝ)) * f (1 / 2) -
    (1 / ((n + 1 : ℕ) : ℝ)) * f (canonicalC3FourCornerUpperPoint n) -
    (1 / (n : ℝ)) * f (canonicalC3FourCornerLowerPoint n) +
    (1 / ((n + 1 : ℕ) : ℝ)) * f (1 / 2)

/-- The centered algebraic moment of the complete four-corner cell. -/
def canonicalC3FourCornerCenteredMoment (n order : ℕ) : ℝ :=
  canonicalC3FourCornerGreenCell n (fun q => (q - 1 / 2) ^ order)

/-- The complete cell has zero total mass. -/
@[simp] theorem canonicalC3FourCornerCenteredMoment_zero (n : ℕ) :
    canonicalC3FourCornerCenteredMoment n 0 = 0 := by
  unfold canonicalC3FourCornerCenteredMoment canonicalC3FourCornerGreenCell
  simp

/-- The complete cell also kills the first centered affine moment. -/
theorem canonicalC3FourCornerCenteredMoment_one
    (n : ℕ) (hn : 0 < n) :
    canonicalC3FourCornerCenteredMoment n 1 = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hn10 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold canonicalC3FourCornerCenteredMoment canonicalC3FourCornerGreenCell
    canonicalC3FourCornerUpperPoint canonicalC3FourCornerLowerPoint
  simp only [pow_one]
  field_simp
  ring

/--
The first nonzero centered moment is quadratic.  This is the exact coefficient
responsible for the second-order tail of the complete Green molecule.
-/
theorem canonicalC3FourCornerCenteredMoment_two
    (n : ℕ) (hn : 0 < n) :
    canonicalC3FourCornerCenteredMoment n 2 =
      -((2 : ℝ) * n + 1) /
        (4 * (n : ℝ) ^ 2 * (((n + 1 : ℕ) : ℝ)) ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hn10 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold canonicalC3FourCornerCenteredMoment canonicalC3FourCornerGreenCell
    canonicalC3FourCornerUpperPoint canonicalC3FourCornerLowerPoint
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one] at *
  ring

/-- The first moment after the centered logarithmic change of coordinates. -/
def canonicalC3FourCornerLogFirstMoment (n : ℕ) : ℝ :=
  canonicalC3FourCornerGreenCell n (fun q => Real.log (2 * q))

/--
The logarithmic first moment is the exact Euler boundary coefficient.  Thus
the affine cancellation in the rational coordinate must not be reused after
the logarithmic change of variables without retaining this term.
-/
theorem canonicalC3FourCornerLogFirstMoment_eq
    (n : ℕ) (hn : 0 < n) :
    canonicalC3FourCornerLogFirstMoment n =
      Real.log ((((n + 1 : ℕ) : ℝ)) / (n : ℝ)) /
        ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hn10 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hn1R
  have hupper :
      2 * canonicalC3FourCornerUpperPoint n =
        (((n + 1 : ℕ) : ℝ)) / (n : ℝ) := by
    unfold canonicalC3FourCornerUpperPoint
    field_simp
  have hlower :
      2 * canonicalC3FourCornerLowerPoint n =
        (n : ℝ) / (((n + 1 : ℕ) : ℝ)) := by
    unfold canonicalC3FourCornerLowerPoint
    field_simp
  have hlogLower :
      Real.log ((n : ℝ) / (((n + 1 : ℕ) : ℝ))) =
        -Real.log ((((n + 1 : ℕ) : ℝ)) / (n : ℝ)) := by
    rw [Real.log_div hn0 hn10, Real.log_div hn10 hn0]
    ring
  unfold canonicalC3FourCornerLogFirstMoment
    canonicalC3FourCornerGreenCell
  simp only
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.log_one,
    hupper, hlower, hlogLower]
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one] at *
  ring

/-! ## Crosswalk to the native `G_pre` four-corner carrier -/

/-- One native `G_pre` corner evaluated on the rational target. -/
def nativeGpreFourCornerTargetTerm
    (edge : ℕ) (corner : GpreCorner) (f : ℝ → ℝ) : ℝ :=
  ((nativeGpreCornerSign corner : ℤ) : ℝ) /
      (nativeGpreCornerV edge corner : ℝ) *
    f ((nativeGpreCornerV edge corner : ℝ) /
      (nativeGpreCornerU edge corner : ℝ))

/--
The complete native target readout.  It keeps the four typed `GpreCorner`
labels separate until the final scalar addition.
-/
def nativeGpreFourCornerTargetCell (edge : ℕ) (f : ℝ → ℝ) : ℝ :=
  nativeGpreFourCornerTargetTerm edge .lowerLeft f +
    nativeGpreFourCornerTargetTerm edge .lowerRight f +
    nativeGpreFourCornerTargetTerm edge .upperLeft f +
    nativeGpreFourCornerTargetTerm edge .upperRight f

/--
The four rational corners recorded by the native `G_pre` carrier synthesize
exactly the complete Green molecule.  No gcd fibre or provenance label is
discarded in defining the source side of this equality.
-/
theorem nativeGpreFourCornerTargetCell_eq_greenCell
    (edge : ℕ) (hedge : 0 < edge) (f : ℝ → ℝ) :
    nativeGpreFourCornerTargetCell edge f =
      canonicalC3FourCornerGreenCell edge f := by
  have hedge0 : (edge : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hedge
  have hedge10 : (((edge + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hll :
      (edge : ℝ) / (2 * (edge : ℝ)) = 1 / 2 := by
    field_simp
  have hlr :
      (((edge + 1 : ℕ) : ℝ)) / (2 * (edge : ℝ)) =
        canonicalC3FourCornerUpperPoint edge := by
    rfl
  have hul :
      (edge : ℝ) / (2 * (edge : ℝ) + 2) =
        canonicalC3FourCornerLowerPoint edge := by
    unfold canonicalC3FourCornerLowerPoint
    norm_num [Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  have hur :
      (((edge + 1 : ℕ) : ℝ)) / (2 * (edge : ℝ) + 2) = 1 / 2 := by
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp
  unfold nativeGpreFourCornerTargetCell nativeGpreFourCornerTargetTerm
    canonicalC3FourCornerGreenCell
  simp only [nativeGpreCornerSign, nativeGpreCornerU,
    nativeGpreCornerV, Int.cast_one, Int.cast_neg]
  norm_num [Nat.cast_add, Nat.cast_one] at hlr hul hur ⊢
  rw [hll, hlr, hul, hur]
  ring

/-- The native four-corner carrier has zero mass. -/
@[simp] theorem nativeGpreFourCornerTargetCell_const_one (edge : ℕ) :
    nativeGpreFourCornerTargetCell edge (fun _ => 1) = 0 := by
  by_cases hedge : edge = 0
  · subst edge
    norm_num [nativeGpreFourCornerTargetCell,
      nativeGpreFourCornerTargetTerm, nativeGpreCornerSign,
      nativeGpreCornerU, nativeGpreCornerV]
  · rw [nativeGpreFourCornerTargetCell_eq_greenCell edge
      (Nat.pos_of_ne_zero hedge)]
    simpa [canonicalC3FourCornerCenteredMoment] using
      canonicalC3FourCornerCenteredMoment_zero edge

/-- The native four-corner carrier kills the centered affine coordinate. -/
theorem nativeGpreFourCornerTargetCell_centered_one
    (edge : ℕ) (hedge : 0 < edge) :
    nativeGpreFourCornerTargetCell edge (fun q => q - 1 / 2) = 0 := by
  rw [nativeGpreFourCornerTargetCell_eq_greenCell edge hedge]
  simpa [canonicalC3FourCornerCenteredMoment] using
    canonicalC3FourCornerCenteredMoment_one edge hedge

/-- The native carrier's exact quadratic centered moment. -/
theorem nativeGpreFourCornerTargetCell_centered_two
    (edge : ℕ) (hedge : 0 < edge) :
    nativeGpreFourCornerTargetCell edge (fun q => (q - 1 / 2) ^ 2) =
      -((2 : ℝ) * edge + 1) /
        (4 * (edge : ℝ) ^ 2 * (((edge + 1 : ℕ) : ℝ)) ^ 2) := by
  rw [nativeGpreFourCornerTargetCell_eq_greenCell edge hedge]
  simpa [canonicalC3FourCornerCenteredMoment] using
    canonicalC3FourCornerCenteredMoment_two edge hedge

/-- The Euler/logarithmic boundary coefficient on the native carrier. -/
theorem nativeGpreFourCornerTargetCell_log
    (edge : ℕ) (hedge : 0 < edge) :
    nativeGpreFourCornerTargetCell edge (fun q => Real.log (2 * q)) =
      Real.log ((((edge + 1 : ℕ) : ℝ)) / (edge : ℝ)) /
        ((edge : ℝ) * (((edge + 1 : ℕ) : ℝ))) := by
  rw [nativeGpreFourCornerTargetCell_eq_greenCell edge hedge]
  exact canonicalC3FourCornerLogFirstMoment_eq edge hedge

/-! ## Universal four-corner product identity -/

/-- Complex scalar synthesis of four provenance-labelled target values. -/
def nativeGpreFourCornerComplexReadout
    (edge : ℕ) (value : GpreCorner → ℂ) : ℂ :=
  (((nativeGpreCornerSign .lowerLeft : ℤ) : ℂ) /
      (nativeGpreCornerV edge .lowerLeft : ℂ)) * value .lowerLeft +
    (((nativeGpreCornerSign .lowerRight : ℤ) : ℂ) /
      (nativeGpreCornerV edge .lowerRight : ℂ)) * value .lowerRight +
    (((nativeGpreCornerSign .upperLeft : ℤ) : ℂ) /
      (nativeGpreCornerV edge .upperLeft : ℂ)) * value .upperLeft +
    (((nativeGpreCornerSign .upperRight : ℤ) : ℂ) /
      (nativeGpreCornerV edge .upperRight : ℂ)) * value .upperRight

/--
Product target before scalar synthesis.  The vertical endpoint is read from
`u / 2`, the horizontal endpoint from `v`, and the factor `v` is retained so
the native target coefficient `sign / v` reconstructs the original product.
-/
def nativeGpreFourCornerProductTarget
    (edge : ℕ) (direct reflected : ℕ → ℂ) (corner : GpreCorner) : ℂ :=
  (nativeGpreCornerV edge corner : ℂ) *
    (starRingEnd ℂ) (direct (nativeGpreCornerU edge corner / 2)) *
    reflected (nativeGpreCornerV edge corner)

/--
Universal four-corner identity: the complete native cell is exactly the
product of two consecutive gradients.  This is the local-to-global
telescoping molecule before any Dirichlet or spectral specialization.
-/
theorem nativeGpreFourCornerComplexReadout_productTarget
    (n : ℕ) (direct reflected : ℕ → ℂ) :
      nativeGpreFourCornerComplexReadout (n + 1)
        (nativeGpreFourCornerProductTarget (n + 1) direct reflected) =
      (starRingEnd ℂ) (direct (n + 2) - direct (n + 1)) *
        (reflected (n + 2) - reflected (n + 1)) := by
  have hn1 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (((n + 2 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (n + 1)
  unfold nativeGpreFourCornerComplexReadout
    nativeGpreFourCornerProductTarget nativeGpreCornerSign
    nativeGpreCornerU nativeGpreCornerV
  norm_num [Nat.cast_add, Nat.cast_one] at *
  let lowerCoefficient : ℂ :=
    (n : ℂ) * ((n : ℂ) + 1)⁻¹ + ((n : ℂ) + 1)⁻¹
  let upperCoefficient : ℂ :=
    (n : ℂ) * ((n : ℂ) + 2)⁻¹ + 2 * ((n : ℂ) + 2)⁻¹
  have hlower : lowerCoefficient = 1 := by
    dsimp [lowerCoefficient]
    calc
      (n : ℂ) * ((n : ℂ) + 1)⁻¹ + ((n : ℂ) + 1)⁻¹ =
          ((n : ℂ) + 1) * ((n : ℂ) + 1)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hn1
  have hupper : upperCoefficient = 1 := by
    dsimp [upperCoefficient]
    calc
      (n : ℂ) * ((n : ℂ) + 2)⁻¹ + 2 * ((n : ℂ) + 2)⁻¹ =
          ((n : ℂ) + 2) * ((n : ℂ) + 2)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hn2
  calc
    _ = lowerCoefficient *
          ((starRingEnd ℂ) (direct (n + 1)) * reflected (n + 1) -
            reflected (n + 1) * (starRingEnd ℂ) (direct (n + 2))) +
        upperCoefficient *
          (-(starRingEnd ℂ) (direct (n + 1)) * reflected (n + 2) +
            reflected (n + 2) * (starRingEnd ℂ) (direct (n + 2))) := by
              dsimp [lowerCoefficient, upperCoefficient]
              ring
    _ = _ := by rw [hlower, hupper]; ring

/-! ## Two-variable polarized kernel before reflection -/

/-- One complete native four-corner cell with independent left/right spectral
parameters.  Conjugation is applied only to the left Dirichlet channel, as in
the ambient complex inner product. -/
def nativeGpreFourCornerPolarizedDirichletCell
    (n : ℕ) (r s : ℂ) : ℂ :=
  nativeGpreFourCornerComplexReadout (n + 1)
    (nativeGpreFourCornerProductTarget (n + 1)
      (natDirichletTerm r) (natDirichletTerm s))

/-- The polarized four-corner cell is exactly one raw gradient Gram entry. -/
theorem nativeGpreFourCornerPolarizedDirichletCell_eq_gradientGram
    (n : ℕ) (r s : ℂ) :
    nativeGpreFourCornerPolarizedDirichletCell n r s =
      (starRingEnd ℂ) (positiveDirichletGradient r n) *
        positiveDirichletGradient s n := by
  rw [nativeGpreFourCornerPolarizedDirichletCell,
    nativeGpreFourCornerComplexReadout_productTarget]
  rfl

/-- Finite two-variable synthesis of complete native four-corner cells. -/
def nativeGpreFourCornerPolarizedDirichletPrefix
    (M : ℕ) (r s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    nativeGpreFourCornerPolarizedDirichletCell n r s

/-- The native four-corner synthesis is exactly the existing raw C3 gamma
kernel, before any reflected or scalar specialization. -/
theorem nativeGpreFourCornerPolarizedDirichletPrefix_eq_rawGammaGram
    (M : ℕ) (r s : ℂ) :
    nativeGpreFourCornerPolarizedDirichletPrefix M r s =
      NativeCarryC3Crosswalk.c3RawGammaGram M r s := by
  unfold nativeGpreFourCornerPolarizedDirichletPrefix
    NativeCarryC3Crosswalk.c3RawGammaGram
  apply Finset.sum_congr rfl
  intro n hn
  exact nativeGpreFourCornerPolarizedDirichletCell_eq_gradientGram n r s

/-- Exact Hilbert realization of the complete finite native cell kernel. -/
theorem nativeGpreFourCornerPolarizedDirichletPrefix_eq_inner
    (M : ℕ) (r s : ℂ) :
    nativeGpreFourCornerPolarizedDirichletPrefix M r s =
      inner ℂ
        (canonicalCompletedC3DirichletGradientPrefixState r M)
        (canonicalCompletedC3DirichletGradientPrefixState s M) := by
  rw [nativeGpreFourCornerPolarizedDirichletPrefix_eq_rawGammaGram,
    c3RawGammaGram_eq_inner_completedPrefix]

/-- Every finite point sample of the complete native cell kernel is positive
semidefinite because it is literally a Gram matrix of prefix states. -/
theorem nativeGpreFourCornerPolarizedDirichletPrefix_posSemidef
    {ι : Type*} [Finite ι] (M : ℕ) (point : ι → ℂ) :
    (Matrix.of fun i j =>
      nativeGpreFourCornerPolarizedDirichletPrefix M
        (point i) (point j)).PosSemidef := by
  have hmatrix :
      (Matrix.of fun i j =>
        nativeGpreFourCornerPolarizedDirichletPrefix M
          (point i) (point j)) =
        Matrix.gram ℂ (fun i =>
          canonicalCompletedC3DirichletGradientPrefixState (point i) M) := by
    ext i j
    exact nativeGpreFourCornerPolarizedDirichletPrefix_eq_inner
      M (point i) (point j)
  rw [hmatrix]
  exact Matrix.posSemidef_gram ℂ _

/-- The two-variable native cell kernel passes to the completed ordinary C3
Gram without changing carrier or inserting a scalar normalization. -/
theorem nativeGpreFourCornerPolarizedDirichletPrefix_tendsto_completed
    {r s : ℂ} (hr : 0 < r.re) (hs : 0 < s.re) :
    Filter.Tendsto
      (fun M : ℕ => nativeGpreFourCornerPolarizedDirichletPrefix M r s)
      Filter.atTop
      (nhds (canonicalCompletedC3RawGammaGram r s hr hs)) := by
  simpa only [nativeGpreFourCornerPolarizedDirichletPrefix_eq_rawGammaGram] using
    c3RawGammaGram_tendsto_completed hr hs

/-- Every finite sample of the completed raw C3 kernel is positive
semidefinite.  This is the infinite-cutoff counterpart of the literal
four-corner prefix Gram. -/
theorem canonicalCompletedC3RawGammaGram_posSemidef
    {ι : Type*} [Finite ι] (point : ι → ℂ)
    (hpoint : ∀ i, 0 < (point i).re) :
    (Matrix.of fun i j =>
      canonicalCompletedC3RawGammaGram
        (point i) (point j) (hpoint i) (hpoint j)).PosSemidef := by
  have hmatrix :
      (Matrix.of fun i j =>
        canonicalCompletedC3RawGammaGram
          (point i) (point j) (hpoint i) (hpoint j)) =
        Matrix.gram ℂ (fun i =>
          canonicalCompletedC3DirichletGradientState
            (point i) (hpoint i)) := by
    ext i j
    rfl
  rw [hmatrix]
  exact Matrix.posSemidef_gram ℂ _

/-! ## Exact ordinary/log-jet reconstruction of the reflected leg -/

/-- Before completion, the reflected leg of every four-corner cell is
reconstructed from the ordinary and logarithmic TFVD coordinates on the same
unreflected edge.  Thus the logarithmic channel enters before scalar
synthesis, not as a correction fitted to the final Gram. -/
theorem
    nativeGpreFourCornerPolarizedDirichletPrefix_reflected_eq_logJetReconstruction
    (M : ℕ) (z w : ℂ) :
    nativeGpreFourCornerPolarizedDirichletPrefix
        M z (reflectedParameter w) =
      ∑ n ∈ Finset.range M,
        (starRingEnd ℂ) (positiveDirichletGradient z n) *
          sameEdgeRecoveredReflectedGradient n
            (positiveDirichletGradient w n)
            (positiveLogDirichletGradient w n) := by
  rw [nativeGpreFourCornerPolarizedDirichletPrefix_eq_rawGammaGram]
  unfold NativeCarryC3Crosswalk.c3RawGammaGram
  apply Finset.sum_congr rfl
  intro n hn
  rw [sameEdgeRecoveredReflectedGradient_canonical]

/-- The same ordinary/log-jet reconstruction survives Hilbert completion.
The target is the complete raw C3 Gram, with no appeal to a scalar Wronskian,
characteristic zero, or positivity hypothesis. -/
theorem nativeGpreFourCornerCompletedReflectedKernel_eq_logJetReconstruction
    (z w : ℂ) (hz : 0 < z.re)
    (hwReflected : 0 < (reflectedParameter w).re) :
    canonicalCompletedC3RawGammaGram
        z (reflectedParameter w) hz hwReflected =
      ∑' n : ℕ,
        (starRingEnd ℂ) (positiveDirichletGradient z n) *
          sameEdgeRecoveredReflectedGradient n
            (positiveDirichletGradient w n)
            (positiveLogDirichletGradient w n) := by
  unfold canonicalCompletedC3RawGammaGram
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [sameEdgeRecoveredReflectedGradient_canonical]
  simp [RCLike.inner_apply]
  ring

/-- The finite native four-corner reconstructions converge directly to the
completed ordinary/log-jet kernel.  This is the cutoff-compatible form of the
preceding identity. -/
theorem
    nativeGpreFourCornerPolarizedDirichletPrefix_reflected_tendsto_logJetReconstruction
    {z w : ℂ} (hz : 0 < z.re)
    (hwReflected : 0 < (reflectedParameter w).re) :
    Filter.Tendsto
      (fun M : ℕ =>
        nativeGpreFourCornerPolarizedDirichletPrefix
          M z (reflectedParameter w))
      Filter.atTop
      (nhds (∑' n : ℕ,
        (starRingEnd ℂ) (positiveDirichletGradient z n) *
          sameEdgeRecoveredReflectedGradient n
            (positiveDirichletGradient w n)
            (positiveLogDirichletGradient w n))) := by
  rw [← nativeGpreFourCornerCompletedReflectedKernel_eq_logJetReconstruction
    z w hz hwReflected]
  exact nativeGpreFourCornerPolarizedDirichletPrefix_tendsto_completed
    hz hwReflected

/--
The universal product cell specialized to the direct/reflected Dirichlet
pair is exactly the existing positive Green edge.
-/
theorem nativeGpreFourCornerDirichletReadout_eq_reflectedGradientEdge
    (n : ℕ) (s : ℂ) :
    nativeGpreFourCornerComplexReadout (n + 1)
        (nativeGpreFourCornerProductTarget (n + 1)
          (natDirichletTerm s)
          (natDirichletTerm (reflectedParameter s))) =
      finiteReflectedGradientEdge n s := by
  rw [nativeGpreFourCornerComplexReadout_productTarget]
  unfold finiteReflectedGradientEdge positiveDirichletGradient
  rfl

/--
The finite TFVD Green edge is the radial tilt times the exact native
four-corner molecule.  The full four-corner provenance is assembled before
the scalar Green readout, and no endpoint or logarithmic channel is removed.
-/
theorem canonicalOrientedCpGreenEdge_eq_radialDifference_mul_gpreCell
    (p : ℕ) (hp : Nat.Prime p) (n : ℕ) (s : ℂ) :
    canonicalOrientedCpGreenEdge p n s =
      ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
        nativeGpreFourCornerComplexReadout (n + 1)
          (nativeGpreFourCornerProductTarget (n + 1)
            (natDirichletTerm s)
            (natDirichletTerm (reflectedParameter s))) := by
  unfold canonicalOrientedCpGreenEdge
  rw [tfvdReflectedGreenWedge_canonicalCpGreenCoordinates,
    phaseNormalizedCpBlockGradient_reflected_eq_radial_mul p hp,
    phaseNormalizedCpBlockGradient_eq_radial_mul p hp,
    nativeGpreFourCornerDirichletReadout_eq_reflectedGradientEdge]
  unfold finiteReflectedGradientEdge
  simp only [map_mul, Complex.conj_ofReal]
  unfold cpRadialDifference
  rw [Complex.ofReal_sub]
  ring

/-! ## Exact finite synthesis and passage to the raw Green limit -/

/-- The complete native four-corner readout has strictly positive real part. -/
theorem nativeGpreFourCornerDirichletReadout_re_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) (n : ℕ) :
    0 < (nativeGpreFourCornerComplexReadout (n + 1)
      (nativeGpreFourCornerProductTarget (n + 1)
        (natDirichletTerm s)
        (natDirichletTerm (reflectedParameter s)))).re := by
  rw [nativeGpreFourCornerDirichletReadout_eq_reflectedGradientEdge]
  exact finiteReflectedGradientEdge_re_pos hs n

/-- Finite synthesis of the complete four-corner native cells. -/
def nativeGpreFourCornerDirichletPrefixReadout (M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    nativeGpreFourCornerComplexReadout (n + 1)
      (nativeGpreFourCornerProductTarget (n + 1)
        (natDirichletTerm s)
        (natDirichletTerm (reflectedParameter s)))

/-- The one-parameter reflected readout is exactly the corresponding
specialization of the two-variable four-corner kernel. -/
theorem nativeGpreFourCornerDirichletPrefixReadout_eq_polarized
    (M : ℕ) (s : ℂ) :
    nativeGpreFourCornerDirichletPrefixReadout M s =
      nativeGpreFourCornerPolarizedDirichletPrefix
        M s (reflectedParameter s) := by
  rfl

/--
The finite native four-corner synthesis is exactly the reflected Green
pairing.  This equality performs the scalar synthesis only after every
four-corner cell has been assembled.
-/
theorem nativeGpreFourCornerDirichletPrefixReadout_eq_pairing
    (M : ℕ) (s : ℂ) :
    nativeGpreFourCornerDirichletPrefixReadout M s =
      finiteReflectedGradientPairing M s := by
  unfold nativeGpreFourCornerDirichletPrefixReadout
    finiteReflectedGradientPairing
  apply Finset.sum_congr rfl
  intro n hn
  exact nativeGpreFourCornerDirichletReadout_eq_reflectedGradientEdge n s

/-- Every nonempty native prefix retains strict Green positivity. -/
theorem nativeGpreFourCornerDirichletPrefixReadout_re_pos
    {M : ℕ} (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < (nativeGpreFourCornerDirichletPrefixReadout M s).re := by
  rw [nativeGpreFourCornerDirichletPrefixReadout_eq_pairing]
  exact finiteReflectedGradientPairing_re_pos hM hs

/--
The finite oriented TFVD Green flux factors through the same native
four-corner prefix, with its canonical radial difference and no manually
introduced normalization.
-/
theorem finiteOrientedCpGreenFlux_eq_radialDifference_mul_gprePrefix
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteOrientedCpGreenFlux p M s =
      ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
        nativeGpreFourCornerDirichletPrefixReadout M s := by
  rw [nativeGpreFourCornerDirichletPrefixReadout_eq_pairing]
  exact finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing p M hp s

/-- The radial tilt energy read directly from the native four-corner carrier. -/
def nativeGpreFourCornerRadialEnergy (p M : ℕ) (s : ℂ) : ℝ :=
  cpRadialCofactor p (criticalDisplacement s.re) *
    (nativeGpreFourCornerDirichletPrefixReadout M s).re

/-- The carrier energy is definitionally the already established Green energy. -/
theorem nativeGpreFourCornerRadialEnergy_eq_finiteRadialGreenEnergy
    (p M : ℕ) (s : ℂ) :
    nativeGpreFourCornerRadialEnergy p M s =
      finiteRadialGreenEnergy p M s := by
  unfold nativeGpreFourCornerRadialEnergy finiteRadialGreenEnergy
  rw [nativeGpreFourCornerDirichletPrefixReadout_eq_pairing]

/-- Strict positivity of the complete finite carrier energy in the strip. -/
theorem nativeGpreFourCornerRadialEnergy_pos
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < nativeGpreFourCornerRadialEnergy p M s := by
  rw [nativeGpreFourCornerRadialEnergy_eq_finiteRadialGreenEnergy]
  exact finiteRadialGreenEnergy_pos p M hp hM hs

/--
The exact finite native carrier converges to the existing infinite reflected
Green pairing.  No independence argument is inferred from this convergence.
-/
theorem nativeGpreFourCornerDirichletPrefixReadout_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ => nativeGpreFourCornerDirichletPrefixReadout M s)
      Filter.atTop (nhds (infiniteReflectedGradientPairing s)) := by
  simpa only [nativeGpreFourCornerDirichletPrefixReadout_eq_pairing] using
    finiteReflectedGradientPairing_tendsto_infinite hs

/-- The reflected Green limit and the completed two-variable four-corner
Gram are the same limit of the same native prefixes. -/
theorem infiniteReflectedGradientPairing_eq_completedFourCornerKernel
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    infiniteReflectedGradientPairing s =
      canonicalCompletedC3RawGammaGram
        s (reflectedParameter s) hs.1
        (by simpa [reflectedParameter] using sub_pos.mpr hs.2) := by
  let hsReflected : 0 < (reflectedParameter s).re := by
    simpa [reflectedParameter] using sub_pos.mpr hs.2
  have hgreen := nativeGpreFourCornerDirichletPrefixReadout_tendsto hs
  have hgramBase :=
    nativeGpreFourCornerPolarizedDirichletPrefix_tendsto_completed
      hs.1 hsReflected
  have hgram : Filter.Tendsto
      (fun M : ℕ => nativeGpreFourCornerDirichletPrefixReadout M s)
      Filter.atTop
      (nhds (canonicalCompletedC3RawGammaGram
        s (reflectedParameter s) hs.1 hsReflected)) := by
    simpa only [nativeGpreFourCornerDirichletPrefixReadout_eq_polarized] using
      hgramBase
  exact tendsto_nhds_unique hgreen hgram

/-- Final all-order spelling of the reflected native limit: the complete
four-corner synthesis is the ordinary/log-jet reconstruction on the same
state, with no scalar Wronskian identification inserted. -/
theorem infiniteReflectedGradientPairing_eq_logJetReconstruction
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    infiniteReflectedGradientPairing s =
      ∑' n : ℕ,
        (starRingEnd ℂ) (positiveDirichletGradient s n) *
          sameEdgeRecoveredReflectedGradient n
            (positiveDirichletGradient s n)
            (positiveLogDirichletGradient s n) := by
  rw [infiniteReflectedGradientPairing_eq_completedFourCornerKernel hs]
  exact nativeGpreFourCornerCompletedReflectedKernel_eq_logJetReconstruction
    s s hs.1 (by simpa [reflectedParameter] using sub_pos.mpr hs.2)

end

end CarrySelfAdjointOperator

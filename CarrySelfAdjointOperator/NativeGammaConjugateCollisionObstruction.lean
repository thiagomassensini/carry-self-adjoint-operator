import CarrySelfAdjointOperator.NativeGammaCenteredDerivative
import CarrySelfAdjointOperator.NativeGammaConjugateCollisionIdentity

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped ComplexConjugate Topology
open Filter Set CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

/-- Only the analytic scalar Wronskian is evaluated at the real center. -/
def nativeConjugateWronskian (t : ℝ) : ℂ :=
  completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion
    (-Complex.I * (t : ℂ)) (Complex.I * (t : ℂ))

theorem nativeConjugateWronskian_zero : nativeConjugateWronskian 0 =
    completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 := by
  simp only [nativeConjugateWronskian, Complex.ofReal_zero, mul_zero]

theorem nativeConjugateWronskian_continuousAt_zero : ContinuousAt nativeConjugateWronskian 0 := by
  have hN := nativeHeightScalar_analyticAt_zero.continuousAt
  have hD := nativeHeightScalar_analyticAt_zero.deriv.continuousAt
  have hNz : ContinuousAt (fun t : ℝ => nativeHeightScalar (Complex.I * (t : ℂ))) 0 :=
    hN.comp_of_eq (by fun_prop) (by simp)
  have hNw : ContinuousAt (fun t : ℝ => nativeHeightScalar (-Complex.I * (t : ℂ))) 0 :=
    hN.comp_of_eq (by fun_prop) (by simp)
  have hDz : ContinuousAt (fun t : ℝ => deriv nativeHeightScalar (Complex.I * (t : ℂ))) 0 :=
    hD.comp_of_eq (by fun_prop) (by simp)
  have hDw : ContinuousAt (fun t : ℝ => deriv nativeHeightScalar (-Complex.I * (t : ℂ))) 0 :=
    hD.comp_of_eq (by fun_prop) (by simp)
  unfold nativeConjugateWronskian completedGreenWronskian nativeHeightScalarBoundaryCompanion
  exact (hDw.neg.mul hNz.star).sub (hNw.mul hDz.neg.star)

theorem nativeConjugateWronskian_eventually_ne_zero :
    ∀ᶠ t : ℝ in 𝓝 0, nativeConjugateWronskian t ≠ 0 := by
  apply nativeConjugateWronskian_continuousAt_zero.eventually_ne
  rw [nativeConjugateWronskian_zero]
  exact nativeHeightScalar_centerWronskian_ne_zero

theorem nativeSourceLocusMismatch_conjugateCounterexampleFamily :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧ ∀ t : ℝ, 0 < t → t < ε →
      ∃ (hz : (Complex.I * (t : ℂ)).im ≠ 0) (hw : (-Complex.I * (t : ℂ)).im ≠ 0),
        operatorHeightParameter (Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
        operatorHeightParameter (-Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
        canonicalCompletedC3NativeSourceLocusProjectionMismatch
          (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 := by
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp nativeConjugateWronskian_eventually_ne_zero
  refine ⟨min δ (1/2), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro t ht hsmall
  have habs : 0 < |t| := by simpa [abs_of_pos ht] using ht
  have hhalf : |t| < 1/2 := by
    rw [abs_of_pos ht]
    exact hsmall.trans_le (min_le_right _ _)
  have ha := nativeImaginaryCollision_admissible t habs hhalf
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, ?_⟩
  rw [nativeSourceLocusMismatch_imaginaryCollision t habs hhalf, neg_ne_zero]
  apply hb
  simpa [Real.dist_eq, abs_of_pos ht] using hsmall.trans_le (min_le_left _ _)

theorem nativeSourceLocusMismatch_counterexamples_arbitrarily_close (δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ t < 1/2 ∧
      ∃ (hz : (Complex.I * (t : ℂ)).im ≠ 0) (hw : (-Complex.I * (t : ℂ)).im ≠ 0),
        operatorHeightParameter (Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
        operatorHeightParameter (-Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
        canonicalCompletedC3NativeSourceLocusProjectionMismatch
          (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 := by
  obtain ⟨ε, hε, hhalf, hf⟩ := nativeSourceLocusMismatch_conjugateCounterexampleFamily
  let t := min ε δ / 2
  have ht : 0 < t := div_pos (lt_min hε hδ) (by norm_num)
  have hmin : t < min ε δ := by dsimp [t]; linarith [lt_min hε hδ]
  have hte := hmin.trans_le (min_le_left _ _)
  exact ⟨t, ht, hmin.trans_le (min_le_right _ _), hte.trans_le hhalf, hf t ht hte⟩

theorem not_canonicalCompletedC3NativeSourceLocusGreenCompatibility :
    ¬ CanonicalCompletedC3NativeSourceLocusGreenCompatibility := by
  intro hcompat
  obtain ⟨t, _, _, _, hz, hw, _, _, hne⟩ :=
    nativeSourceLocusMismatch_counterexamples_arbitrarily_close 1 (by norm_num)
  exact hne ((canonicalCompletedC3NativeSourceLocusGreenCompatibility_iff_mismatch_zero.mp hcompat)
    _ _ hz hw)

theorem not_nativeSourceLocusGreenCompatibility_genuineStrip :
    ¬ (∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
      operatorHeightParameter z ∈ genuineCriticalStrip →
      operatorHeightParameter w ∈ genuineCriticalStrip →
      CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt z w hz hw) := by
  intro hcompat
  obtain ⟨t, _, _, _, hz, hw, hs, hws, hne⟩ :=
    nativeSourceLocusMismatch_counterexamples_arbitrarily_close 1 (by norm_num)
  apply hne
  exact sub_eq_zero.mpr (hcompat _ _ hz hw hs hws)

/-- Gamma is used only at nonreal admissible parameters, never at zero. -/
abbrev NativeCollisionParameter := {t : ℝ // 0 < |t| ∧ |t| < 1/2}

theorem nativeCollisionParameter_filter_neBot :
    NeBot (comap (fun t : NativeCollisionParameter => t.val) (𝓝 (0 : ℝ))) := by
  apply comap_neBot
  intro s hs
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  let t := min δ (1/2) / 2
  have ht : 0 < t := div_pos (lt_min hδ (by norm_num)) (by norm_num)
  have hmin : t < min δ (1/2) := by dsimp [t]; linarith [lt_min hδ (by norm_num : (0 : ℝ) < 1/2)]
  have ha : 0 < |t| ∧ |t| < 1/2 := by
    rw [abs_of_pos ht]
    exact ⟨ht, hmin.trans_le (min_le_right _ _)⟩
  refine ⟨⟨t, ha⟩, hball ?_⟩
  change dist t 0 < δ
  simpa [Real.dist_eq, abs_of_pos ht] using hmin.trans_le (min_le_left _ _)

theorem nativeSourceLocusMismatch_conjugateCollision_tendsto :
    Tendsto (fun t : NativeCollisionParameter =>
      canonicalCompletedC3NativeSourceLocusProjectionMismatch
        (Complex.I * (t.val : ℂ)) (-Complex.I * (t.val : ℂ))
        (nativeImaginaryCollision_admissible t.val t.property.1 t.property.2).1
        (nativeImaginaryCollision_admissible t.val t.property.1 t.property.2).2.1)
      (comap (fun t : NativeCollisionParameter => t.val) (𝓝 (0 : ℝ)))
      (𝓝 (2 * nativeHeightScalar 0 * deriv nativeHeightScalar 0)) := by
  have heq : (fun t : NativeCollisionParameter =>
      canonicalCompletedC3NativeSourceLocusProjectionMismatch
        (Complex.I * (t.val : ℂ)) (-Complex.I * (t.val : ℂ))
        (nativeImaginaryCollision_admissible t.val t.property.1 t.property.2).1
        (nativeImaginaryCollision_admissible t.val t.property.1 t.property.2).2.1) =
      (fun t => -nativeConjugateWronskian t.val) := by
    funext t
    exact nativeSourceLocusMismatch_imaginaryCollision t.val t.property.1 t.property.2 _ _
  rw [heq]
  have ht : Tendsto (fun t : NativeCollisionParameter => t.val)
      (comap (fun t : NativeCollisionParameter => t.val) (𝓝 (0 : ℝ))) (𝓝 (0 : ℝ)) := tendsto_comap
  have h := nativeConjugateWronskian_continuousAt_zero.neg.tendsto.comp ht
  have hc : -nativeConjugateWronskian 0 = 2 * nativeHeightScalar 0 * deriv nativeHeightScalar 0 := by
    rw [nativeConjugateWronskian_zero, nativeHeightScalar_centerWronskian_eq]
    ring
  dsimp only [Function.comp_def, Pi.neg_apply] at h
  rwa [hc] at h

end
end CarrySelfAdjointOperator.GammaMaterialSewing

import CarrySelfAdjointOperator.PrimeDepthNormalizedResponseVectorJet

/-!
# Rank of the normalized finite trace lift

The four geometric sectors retain their labels, but each sector has already
been projected to three complex trace pairs. This finite carrier supports the
proved all-order linear readout; it cannot supply arbitrarily many independent
energy columns by a fixed linear map, even into an infinite-dimensional L2.
This is a restriction on this compressed candidate, not on the native source.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem finrank_complex_completedFullWronskianTrace :
    Module.finrank ℂ CanonicalCompletedC3FullWronskianOperatorCarrier = 6 := by
  change Module.finrank ℂ
      (WithLp 2 (WithLp 2 (ℂ × ℂ) ×
        WithLp 2 (WithLp 2 (ℂ × ℂ) × WithLp 2 (ℂ × ℂ)))) = 6
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_prod]
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq]
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_prod]
  rw [Module.finrank_prod]
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq]
  simp

theorem finrank_complex_completedPrimeDepthJetCarrier :
    Module.finrank ℂ CompletedPrimeDepthJetCarrier = 24 := by
  change Module.finrank ℂ (WithLp 2 (CanonicalCompletedC3StructuralChannel →
    CanonicalCompletedC3FullWronskianOperatorCarrier)) = 24
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  simp only [finrank_complex_completedFullWronskianTrace, Finset.sum_const,
    Finset.card_univ]
  have hc : Fintype.card CanonicalCompletedC3StructuralChannel = 4 := by decide
  norm_num [hc]

/-- Any fixed linear transformation of these source trace jets has rank at
most 24, even if its target is an infinite-dimensional physical carrier. -/
theorem normalizedResponseVectorJet_transformed_not_independent
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (T : CompletedPrimeDepthJetCarrier →ₗ[ℂ] H) :
    ¬ LinearIndependent ℂ (fun i : Fin 25 => T (primeDepthNormalizedResponseVectorJet i.val)) := by
  intro h
  have hi : LinearIndependent ℂ (fun i : Fin 25 => primeDepthNormalizedResponseVectorJet i.val) :=
    LinearIndependent.of_comp T h
  have hc := hi.fintype_card_le_finrank
  rw [finrank_complex_completedPrimeDepthJetCarrier] at hc
  norm_num at hc

/-- A nonzero coefficient family is annihilated before any norm is taken.
No native positivity premise or target Gram is used. -/
theorem normalizedResponseVectorJet_transformed_has_dependency
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (T : CompletedPrimeDepthJetCarrier →ₗ[ℂ] H) :
    ∃ c : Fin 25 → ℂ, c ≠ 0 ∧
      ∑ i : Fin 25, c i • T (primeDepthNormalizedResponseVectorJet i.val) = 0 := by
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp
    (normalizedResponseVectorJet_transformed_not_independent T)
  exact ⟨c, fun h => hi (congrFun h i), hc⟩

/-- Such a fixed transform cannot by itself prove strict energy on all
nonzero combinations. This restriction does not apply to an infinite source
state, including a construction using the whole jet tower. -/
theorem normalizedResponseVectorJet_no_strict_all_order_energy
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : CompletedPrimeDepthJetCarrier →ₗ[ℂ] H) :
    ¬ (∀ c : Fin 25 → ℂ, c ≠ 0 →
      0 < ‖∑ i : Fin 25, c i • T (primeDepthNormalizedResponseVectorJet i.val)‖^2) := by
  intro hp
  obtain ⟨c, hc, hz⟩ := normalizedResponseVectorJet_transformed_has_dependency T
  have h := hp c hc
  simp [hz] at h

end
end CarrySelfAdjointOperator

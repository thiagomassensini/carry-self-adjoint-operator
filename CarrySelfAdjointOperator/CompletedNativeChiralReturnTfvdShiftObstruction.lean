import CarrySelfAdjointOperator.CompletedNativeChiralReturnFiniteTransfer

/-!
# The finite TFVD shift is not the completed chiral return

The notebook's positive boundary defect belongs to a truncating shift.
An invertible TFVD analysis does not remove its lack of nonzero eigenvalues.
The actual source return multiplies each incident coefficient by its own
completed quotient, which is nonzero near the centered source germ.
This local obstruction is independent of metrics and sign certificates.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- The literal zero-boundary shift from the finite TFVD transport note.
This auxiliary test operator is not the native return or a depth clock. -/
def finiteTfvdTruncatingShift (M : ℕ) : (Fin M → ℂ) →ₗ[ℂ] (Fin M → ℂ) where
  toFun x i := if h : 0 < (i : ℕ) then x ⟨(i : ℕ)-1, by omega⟩ else 0
  map_add' x y := by
    funext i
    dsimp only [Pi.add_apply]
    by_cases h : 0 < (i : ℕ) <;> simp [h]
  map_smul' a x := by
    funext i
    dsimp only [Pi.smul_apply]
    by_cases h : 0 < (i : ℕ) <;> simp [h]

/-- No nonzero eigenvalue survives the truncating boundary. This proof
retains the whole finite vector and does not assume any energy inequality. -/
theorem finiteTfvdTruncatingShift_eigenvector_eq_zero (M : ℕ)
    (x : Fin M → ℂ) (a : ℂ) (ha : a ≠ 0)
    (he : finiteTfvdTruncatingShift M x = a • x) : x = 0 := by
  have hx : ∀ n : ℕ, ∀ hn : n < M, x ⟨n, hn⟩ = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hcoord := congrFun he ⟨n, hn⟩
      by_cases hpos : 0 < n
      · have hprev := ih (n-1) (by omega) (by omega)
        simpa [finiteTfvdTruncatingShift, hpos, hprev, ha] using hcoord.symm
      · have hn0 : n = 0 := by omega
        subst n
        simpa [finiteTfvdTruncatingShift, ha] using hcoord.symm
  funext i
  exact hx i i.isLt

/-- The source quotient is nonzero eventually at each original radial node.
Only source continuity and the centered value -1 are used. -/
theorem nativeRadialChiralQuotient_eventually_ne_zero (i : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      completedNativeHermiteBiehlerChiralQuotient
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
  have hcenter : completedNativeHermiteBiehlerChiralQuotient 0 ≠ 0 := by simp
  exact (canonicalCompletedC3RadialTiltPoint_tendsto_zero i).eventually
    (hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero_raw.continuousAt.eventually_ne hcenter)

/-- In the exact native incident coordinates, no injective map can send the
return to a finite truncating shift with any invertible TFVD chart. The
chart is unrestricted: this also excludes the geometrically specified one. -/
theorem radialReturn_no_finiteTfvdShift_intertwiner (k N M : ℕ)
    (i : Fin N)
    (hq : completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (analysis : (Fin M → ℂ) ≃ₗ[ℂ] (Fin M → ℂ)) :
    ¬ ∃ U : (Fin N → ℂ) →ₗ[ℂ] (Fin M → ℂ), Function.Injective U ∧
      ∀ c : Fin N → ℂ,
        U (fun j => c j * completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k j)) =
        analysis (finiteTfvdTruncatingShift M (analysis.symm (U c))) := by
  classical
  rintro ⟨U, hU, hintertwine⟩
  let a := completedNativeHermiteBiehlerChiralQuotient
    (canonicalCompletedC3RadialTiltPoint k i)
  let e : Fin N → ℂ := Pi.single i 1
  have hmult : (fun j => e j * completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k j)) = a • e := by
    funext j
    by_cases h : i = j
    · subst j; simp [e, a]
    · simp [e, Ne.symm h]
  have h := hintertwine e
  rw [hmult, U.map_smul] at h
  have he : finiteTfvdTruncatingShift M (analysis.symm (U e)) =
      a • analysis.symm (U e) := by
    have ht := congrArg analysis.symm h
    simpa using ht.symm
  have hz := finiteTfvdTruncatingShift_eigenvector_eq_zero M
    (analysis.symm (U e)) a hq he
  have hue : U e = 0 := by
    have ht := congrArg analysis hz
    simpa using ht
  have hezero : e = 0 := hU (hue.trans U.map_zero.symm)
  have hi := congrFun hezero i
  simp [e] at hi

/-- Every nonempty native finite source rules out this shift realization
under one eventual threshold, for every target cutoff and every invertible
analysis. This does not rule out a different conservative ambient return. -/
theorem radialReturn_eventually_no_finiteTfvdShift_intertwiner
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ k : ℕ in atTop, ∀ M : ℕ,
      ∀ analysis : (Fin M → ℂ) ≃ₗ[ℂ] (Fin M → ℂ),
        ¬ ∃ U : (Fin N → ℂ) →ₗ[ℂ] (Fin M → ℂ), Function.Injective U ∧
          ∀ c : Fin N → ℂ,
            U (fun j => c j * completedNativeHermiteBiehlerChiralQuotient
              (canonicalCompletedC3RadialTiltPoint k j)) =
            analysis (finiteTfvdTruncatingShift M (analysis.symm (U c))) := by
  filter_upwards [nativeRadialChiralQuotient_eventually_ne_zero 0] with k hk
  intro M analysis
  exact radialReturn_no_finiteTfvdShift_intertwiner k N M ⟨0, hN⟩ hk analysis


/-- The same obstruction on the ACTUAL incident Cauchy span, using the
existing exact return rather than a newly proposed coefficient operator.
The returned vector remains in this span by its already proved synthesis. -/
theorem radialReturn_eventually_no_finiteTfvdShift_spanIntertwiner
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ k : ℕ in atTop, ∀ M : ℕ,
      ∀ analysis : (Fin M → ℂ) ≃ₗ[ℂ] (Fin M → ℂ),
        ¬ ∃ U : RadialIncidentSpan k N →ₗ[ℂ] (Fin M → ℂ), Function.Injective U ∧
          ∀ x : RadialIncidentSpan k N,
            U ⟨radialReturnTransfer k N x, radialReturnTransfer_mem_incidentSpan k N x⟩ =
            analysis (finiteTfvdTruncatingShift M (analysis.symm (U x))) := by
  filter_upwards [radialReturn_eventually_no_finiteTfvdShift_intertwiner N hN] with k hk
  intro M analysis
  rintro ⟨U, hU, haction⟩
  apply hk M analysis
  let J := U.comp (radialIncidentCoordinates k N).symm.toLinearMap
  refine ⟨J, hU.comp (radialIncidentCoordinates k N).symm.injective, ?_⟩
  intro c
  have h := haction (radialIncidentVector k N c)
  have he : (⟨radialReturnTransfer k N (radialIncidentVector k N c),
      radialReturnTransfer_mem_incidentSpan k N (radialIncidentVector k N c)⟩ :
      RadialIncidentSpan k N) = radialIncidentVector k N
        (fun j => c j * completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k j)) := by
    apply Subtype.ext
    change radialReturnTransfer k N (radialIncidentVector k N c) =
      radialIncidentSynthesis k N (fun j => c j *
        completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k j))
    rw [radialReturnTransfer_exact, radialReturnedSynthesis_eq_incident_multiply]
  rw [he] at h
  exact h

end
end CarrySelfAdjointOperator.ChiralReturn

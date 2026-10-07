import CarrySelfAdjointOperator.CompletedC3EnrichedSymplecticNoLeakBridge
import CPFormal.Analytic.CpFiniteTfvdLogJetResidualCutoff

/-!
# Reflected same-edge log-jet ledger versus the current adjacent-edge mixed form

The existing mixed carrier retains the ordinary/log-jet pairs at w and
reflected z. Observe their historical sesquilinear same-edge wedge before
synthesis, with all three material edges retained. This is not a new metric
or a replacement for the carrier. The reflected specialization reuses the
old commutator AND vertex/cutoff residual. A canonical finite-prefix canary
then tests whether this observation equals the current mixed provenance.
-/
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary
open scoped ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false

/-- Historical conjugated same-edge observation of two retained role pairs. -/
def canonicalC3ReflectedLogRoleEdge
    (x : CanonicalC3AllCutoffMixedSourceHilbert) (n : ℕ) : ℂ :=
  reflectedLogJetEdgeWedge (x.wSource.1 n) (x.wSource.2 n)
    (x.reflectedZSource.1 n) (x.reflectedZSource.2 n)

/-- All three consecutive material edges, before scalar synthesis. -/
def canonicalC3ReflectedLogRoleTriple
    (x : CanonicalC3AllCutoffMixedSourceHilbert) (m : ℕ) : TfvdWedgeTriple :=
  { first := canonicalC3ReflectedLogRoleEdge x (3 * m)
    second := canonicalC3ReflectedLogRoleEdge x (3 * m + 1)
    dormant := canonicalC3ReflectedLogRoleEdge x (3 * m + 2) }

/-- Finite synthesis uses the existing three-role total only at the end. -/
def canonicalC3ReflectedLogRoleTrace
    (M : ℕ) (x : CanonicalC3AllCutoffMixedSourceHilbert) : ℂ :=
  ∑ m ∈ Finset.range M, (canonicalC3ReflectedLogRoleTriple x m).total

/-- Two independent parameters remain independent; reflection is literal.
This is a same-edge sesquilinear form, not the adjacent-edge mixed wedge. -/
theorem canonicalC3ReflectedLogRoleEdge_prefix
    (M : ℕ) (z w : ℂ) {n : ℕ} (hn : n < 3 * M) :
    canonicalC3ReflectedLogRoleEdge (canonicalC3AllCutoffMixedSourcePrefixState M z w) n =
      reflectedLogJetEdgeWedge
        (positiveDirichletGradient w n) (positiveLogDirichletGradient w n)
        (positiveDirichletGradient (reflectedParameter z) n)
        (positiveLogDirichletGradient (reflectedParameter z) n) := by
  simp [canonicalC3ReflectedLogRoleEdge,
    canonicalC3AllCutoffMixedSourcePrefixState_wSource,
    canonicalC3AllCutoffMixedSourcePrefixState_reflectedZSource,
    canonicalCompletedC3HilbertPrefixState, hn]

/-- Reflected specialization recovers the old triple literally. -/
theorem canonicalC3ReflectedLogRoleTriple_prefix_eq_historical
    (M : ℕ) (s : ℂ) {m : ℕ} (hm : m < M) :
    canonicalC3ReflectedLogRoleTriple (canonicalC3AllCutoffMixedSourcePrefixState M s s) m =
      canonicalReflectedLogJetWedgeTriple m s := by
  apply TfvdWedgeTriple.ext <;>
    simp only [canonicalC3ReflectedLogRoleTriple, canonicalReflectedLogJetWedgeTriple,
      canonicalReflectedLogJetEdgeWedge]
  · exact canonicalC3ReflectedLogRoleEdge_prefix M s s (by omega)
  · exact canonicalC3ReflectedLogRoleEdge_prefix M s s (by omega)
  · exact canonicalC3ReflectedLogRoleEdge_prefix M s s (by omega)

/-- The pre-synthesis triple survives the historical enriched TFVD roundtrip. -/
theorem canonicalC3ReflectedLogRoleTriple_prefix_eq_enriched
    (M : ℕ) (s : ℂ) {m : ℕ} (hm : m < M) :
    canonicalC3ReflectedLogRoleTriple (canonicalC3AllCutoffMixedSourcePrefixState M s s) m =
      canonicalEnrichedTfvdReflectedLogJetWedgeTriple tfvdHaarScale (fun _ => 1) m s := by
  rw [canonicalC3ReflectedLogRoleTriple_prefix_eq_historical M s hm,
    canonicalEnrichedTfvdReflectedLogJetWedgeTriple_eq_canonical
      tfvdHaarScale_ne_zero (fun _ => 1) m (by norm_num) s]

/-- The defect on each retained role uses both the commutator and residual.
The Green term is retained separately; no sign or cancellation is assumed. -/
theorem canonicalC3ReflectedLogRoleTriple_prefix_decomposition
    (M : ℕ) (s : ℂ) {m : ℕ} (hm : m < M) :
    canonicalC3ReflectedLogRoleTriple (canonicalC3AllCutoffMixedSourcePrefixState M s s) m =
      TfvdWedgeTriple.add (canonicalCpGreenWedgeTriple 3 m s)
        (TfvdWedgeTriple.add (canonicalReflectedCpLogJetCommutatorWedgeTriple 3 m s)
          (canonicalLogJetCommutatorResidualTriple 3 m s)) := by
  rw [canonicalC3ReflectedLogRoleTriple_prefix_eq_historical M s hm,
    canonicalReflectedLogJetWedgeTriple_eq_green_add_defect,
    canonicalLogJetGreenDefectTriple_eq_commutator_add_residual 3 (by norm_num)]

/-- Only after retaining the triple do we synthesize the whole finite prefix. -/
theorem canonicalC3ReflectedLogRoleTrace_prefix_eq_vertexFlux
    (M : ℕ) (s : ℂ) :
    canonicalC3ReflectedLogRoleTrace M (canonicalC3AllCutoffMixedSourcePrefixState M s s) =
      finiteReflectedLogJetVertexFlux (3 * M) s := by
  unfold canonicalC3ReflectedLogRoleTrace
  have h : (∑ m ∈ Finset.range M,
      (canonicalC3ReflectedLogRoleTriple (canonicalC3AllCutoffMixedSourcePrefixState M s s) m).total) =
      ∑ m ∈ Finset.range M, (canonicalReflectedLogJetWedgeTriple m s).total := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [canonicalC3ReflectedLogRoleTriple_prefix_eq_historical M s (Finset.mem_range.mp hm)]
  rw [h]
  unfold TfvdWedgeTriple.total canonicalReflectedLogJetWedgeTriple
  change (∑ m ∈ Finset.range M,
    (canonicalReflectedLogJetEdgeWedge (3*m) s +
      canonicalReflectedLogJetEdgeWedge (3*m+1) s +
      canonicalReflectedLogJetEdgeWedge (3*m+2) s)) = _
  rw [sum_range_threeBlocks_eq_range (fun n => canonicalReflectedLogJetEdgeWedge n s) M]
  simp_rw [canonicalReflectedLogJetEdgeWedge_eq_vertexFlux]
  rfl

/-- Whole-prefix Green plus commutator plus residual; no term is discarded. -/
theorem canonicalC3ReflectedLogRoleTrace_prefix_decomposition
    (M : ℕ) (s : ℂ) :
    canonicalC3ReflectedLogRoleTrace M (canonicalC3AllCutoffMixedSourcePrefixState M s s) =
      finiteOrientedCpGreenFlux 3 (3 * M) s +
        (finiteCanonicalCpLogJetCommutatorWedgeTrace 3 M s +
          finiteCanonicalLogJetCommutatorResidualTrace 3 M s) := by
  rw [← finiteCanonicalLogJetGreenDefectTrace_eq_commutator_add_residual 3 (by norm_num),
    finiteCanonicalLogJetGreenDefectTrace_eq_vertex_sub_green,
    canonicalC3ReflectedLogRoleTrace_prefix_eq_vertexFlux]
  ring

/-- The old exact boundary/cross-bulk split, with its moving endpoint retained. -/
theorem canonicalC3ReflectedLogRoleTrace_prefix_eq_cutoff_add_bulk
    (M : ℕ) (s : ℂ) :
    canonicalC3ReflectedLogRoleTrace M (canonicalC3AllCutoffMixedSourcePrefixState M s s) =
      reflectedLogJetMovingCutoff (3 * M) s + finiteReflectedLogJetCrossBulk (3 * M) s := by
  rw [canonicalC3ReflectedLogRoleTrace_prefix_eq_vertexFlux,
    finiteReflectedLogJetVertexFlux_eq_cutoff_add_crossBulk]

/-- An exact finite algebraic canary at s=0, not a critical-strip limit. -/
theorem canonicalC3ReflectedLogRoleTrace_one_zero :
    canonicalC3ReflectedLogRoleTrace 1 (canonicalC3AllCutoffMixedSourcePrefixState 1 0 0) =
      ((-(Real.log 4) / 12 - Real.log 2 / 3 - Real.log 3 / 12 : ℝ) : ℂ) := by
  rw [canonicalC3ReflectedLogRoleTrace_prefix_eq_cutoff_add_bulk]
  norm_num [reflectedLogJetMovingCutoff, positiveLogVertexWeight,
    reflectedDirichletVertexCrossFlux_two_zero, finiteReflectedLogJetCrossBulk_three_zero]
  ring

/-- In the current adjacent-edge mixed form the w ordinary prefix is zero.
Its Green port is zero as well, so all mixed wedges vanish. -/
theorem canonicalC3CurrentMixedProvenance_one_zero :
    CanonicalC3AllCutoffMixedSourceHilbert.greenProvenanceReadout
      1 0 (reflectedParameter 0) (canonicalC3AllCutoffMixedSourcePrefixState 1 0 0) = 0 := by
  have hg : canonicalCompletedC3DirichletGradientPrefixState (0 : ℂ) 3 = 0 := by
    ext n
    simp [canonicalCompletedC3DirichletGradientPrefixState_apply,
      positiveDirichletGradient, natDirichletTerm, dirichletTerm]
  have hz : (WithLp.toLp 2 (fun _ : Fin 3 => (0 : ℂ)) :
      NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3) = 0 := rfl
  have hc (a : Fin 2) : Fin.cases (motive := fun _ : Fin 2 => ℂ) 0 (fun _ => 0) a = 0 := by
    fin_cases a <;> rfl
  simp [CanonicalC3AllCutoffMixedSourceHilbert.greenProvenanceReadout,
    CanonicalC3AllCutoffMixedSourceHilbert.mixedLegs,
    CanonicalC3AllCutoffMixedSourceHilbert.greenPort,
    canonicalC3AllCutoffMixedSourcePrefixState_wSource,
    canonicalCompletedC3HilbertPrefixState, hg, hc, hz, greenForm, sameSEdgeBoundaryWedge]

/-- Even on canonical finite prefixes, the two historical/current observations
cannot be identified universally. This says nothing about completed limits. -/
theorem canonicalC3ReflectedLogRoleTrace_ne_currentMixedProvenance_one_zero :
    canonicalC3ReflectedLogRoleTrace 1 (canonicalC3AllCutoffMixedSourcePrefixState 1 0 0) ≠
      CanonicalC3AllCutoffMixedSourceHilbert.greenProvenanceReadout
        1 0 (reflectedParameter 0) (canonicalC3AllCutoffMixedSourcePrefixState 1 0 0) := by
  rw [canonicalC3ReflectedLogRoleTrace_one_zero, canonicalC3CurrentMixedProvenance_one_zero]
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hne : -(Real.log 4) / 12 - Real.log 2 / 3 - Real.log 3 / 12 ≠ 0 := by
    nlinarith
  exact_mod_cast hne

end
end CarrySelfAdjointOperator

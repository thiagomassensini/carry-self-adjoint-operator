import CarrySelfAdjointOperator.CompletedNativeCameraResolvedOrdinaryGradientPromotion
import CarrySelfAdjointOperator.BR2EnrichedPreRecoveryCorrelationCanary
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Fixed global seed plus six-role analysis variation

The existing BR2 linear interface targets gradient analyses, not the global
ordinary seed. It is retained. The complete seeded source is represented
here by standard products: one global boundary coordinate and one unchanged
TFVD datum at each source role. No seed is assigned to an external camera.

Assembly is affine with an explicit linear variation part. The zero-input
obstruction applies only to a homogeneous map into this complete seeded
carrier, not to the original gradient-analysis interface. No BR2-to-role
variation is chosen by this file.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Standard product coordinates for the complete source role, retaining the
global boundary seed outside the TFVD analysis carrier. No metric is added. -/
abbrev CanonicalC3AffineSixRoleAnalysisCarrier
    (S : Finset NativeGpreBoundaryContext) :=
  CanonicalC3SixSourceRole → (ℂ × NativeGpreFiniteTfvdAnalysisCarrier S)

/-- Bundle the already existing role view as a real-linear map. Source
parameter/channel roles remain the same; they are not camera slots. -/
def canonicalC3SixSourceRoleAnalysisLinearMap
    (S : Finset NativeGpreBoundaryContext) :
    CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S →ₗ[ℝ]
      (CanonicalC3SixSourceRole → NativeGpreFiniteTfvdAnalysisCarrier S) where
  toFun := canonicalC3SixSourceRoleAnalysis S
  map_add' x y := by
    funext role
    rcases role with ⟨parameter, channel⟩
    cases parameter <;> cases channel <;> rfl
  map_smul' c x := by
    funext role
    rcases role with ⟨parameter, channel⟩
    cases parameter <;> cases channel <;> rfl

/-- The fixed seed is the actual global Dirichlet atom. Ordinary roles retain
it; logJet roles receive zero. The analysis component is zero. -/
def canonicalC3SixSourceFixedRoleSeed
    (S : Finset NativeGpreBoundaryContext) : CanonicalC3AffineSixRoleAnalysisCarrier S :=
  fun role =>
    (if role.2 = .ordinary then canonicalOrdinaryBoundarySeed 0 else 0, 0)

/-- Include homogeneous role variations without adding any boundary atom. -/
def canonicalC3SixSourceRoleVariationEmbedding
    (S : Finset NativeGpreBoundaryContext) :
    (CanonicalC3SixSourceRole → NativeGpreFiniteTfvdAnalysisCarrier S) →ₗ[ℝ]
      CanonicalC3AffineSixRoleAnalysisCarrier S where
  toFun := fun variation role => (0, variation role)
  map_add' x y := by
    funext role
    apply Prod.ext <;> simp
  map_smul' c x := by
    funext role
    apply Prod.ext <;> simp

/-- Honest seeded assembly: fixed global boundary plus linear analysis
variation. This is a standard affine map, not a new source certificate. -/
def canonicalC3SixSourceRoleAffineAssembly
    (S : Finset NativeGpreBoundaryContext) :
    (CanonicalC3SixSourceRole → NativeGpreFiniteTfvdAnalysisCarrier S) →ᵃ[ℝ]
      CanonicalC3AffineSixRoleAnalysisCarrier S where
  toFun := fun variation => canonicalC3SixSourceFixedRoleSeed S +
    canonicalC3SixSourceRoleVariationEmbedding S variation
  linear := canonicalC3SixSourceRoleVariationEmbedding S
  map_vadd' p v := by
    change canonicalC3SixSourceFixedRoleSeed S +
        canonicalC3SixSourceRoleVariationEmbedding S (v + p) =
      canonicalC3SixSourceRoleVariationEmbedding S v +
        (canonicalC3SixSourceFixedRoleSeed S +
          canonicalC3SixSourceRoleVariationEmbedding S p)
    rw [map_add]
    abel

/-- Boundary coordinates are fixed precisely at ordinary roles. -/
theorem canonicalC3SixSourceRoleAffineAssembly_seed
    (S : Finset NativeGpreBoundaryContext)
    (variation : CanonicalC3SixSourceRole → NativeGpreFiniteTfvdAnalysisCarrier S)
    (role : CanonicalC3SixSourceRole) :
    (canonicalC3SixSourceRoleAffineAssembly S variation role).1 =
      if role.2 = .ordinary then 1 else 0 := by
  simp [canonicalC3SixSourceRoleAffineAssembly, canonicalC3SixSourceFixedRoleSeed,
    canonicalC3SixSourceRoleVariationEmbedding, canonicalOrdinaryBoundarySeed_eq_one]

/-- Assembly preserves the complete variation datum, including its trace and
both G-pre roles. It does not identify a G-pre role with a six-source role. -/
theorem canonicalC3SixSourceRoleAffineAssembly_analysis
    (S : Finset NativeGpreBoundaryContext)
    (variation : CanonicalC3SixSourceRole → NativeGpreFiniteTfvdAnalysisCarrier S)
    (role : CanonicalC3SixSourceRole) :
    (canonicalC3SixSourceRoleAffineAssembly S variation role).2 = variation role := by
  simp [canonicalC3SixSourceRoleAffineAssembly, canonicalC3SixSourceFixedRoleSeed,
    canonicalC3SixSourceRoleVariationEmbedding]

/-- The seed cancels on differences; only the already specified linear
variation remains. No linearity in the analytic parameters is claimed. -/
theorem canonicalC3SixSourceRoleAffineAssembly_sub
    (S : Finset NativeGpreBoundaryContext)
    (v w : CanonicalC3SixSourceRole → NativeGpreFiniteTfvdAnalysisCarrier S) :
    canonicalC3SixSourceRoleAffineAssembly S v -
        canonicalC3SixSourceRoleAffineAssembly S w =
      canonicalC3SixSourceRoleVariationEmbedding S (v - w) := by
  change (canonicalC3SixSourceFixedRoleSeed S +
      canonicalC3SixSourceRoleVariationEmbedding S v) -
    (canonicalC3SixSourceFixedRoleSeed S +
      canonicalC3SixSourceRoleVariationEmbedding S w) = _
  rw [map_sub]
  abel

/-- The actual canonical source with its true seed exposed outside each
ordinary gradient analysis. All six original analyses remain unchanged. -/
def canonicalC3SixSourceAffineRoleState
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    CanonicalC3AffineSixRoleAnalysisCarrier S :=
  fun role =>
    (if role.2 = .ordinary then
      canonicalOrdinaryBoundarySeed (canonicalC3SixSourceParameterValue z w role.1)
      else 0,
     canonicalC3SixSourceRoleAnalysis S
       (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) role)

/-- Exact canonical fixed-seed plus variation decomposition. -/
theorem canonicalC3SixSourceAffineRoleState_eq_fixedSeed_add_variation
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    canonicalC3SixSourceAffineRoleState M q S z w =
      canonicalC3SixSourceFixedRoleSeed S +
        canonicalC3SixSourceRoleVariationEmbedding S
          (canonicalC3SixSourceRoleAnalysis S
            (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w)) := by
  funext role
  apply Prod.ext
  · simp [canonicalC3SixSourceAffineRoleState, canonicalC3SixSourceFixedRoleSeed,
      canonicalC3SixSourceRoleVariationEmbedding, canonicalOrdinaryBoundarySeed_eq_one]
  · simp [canonicalC3SixSourceAffineRoleState, canonicalC3SixSourceFixedRoleSeed,
      canonicalC3SixSourceRoleVariationEmbedding]

/-- Compatibility with the existing boundary-aware camera ledger. Camera
synthesis is used only in this comparison theorem; no source transport or
role-to-camera identification is defined by it. -/
theorem canonicalC3SixSourceAffineRoleState_eq_existing_cameraLedger
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ)
    (role : CanonicalC3SixSourceRole) :
    canonicalC3SixSourceAffineRoleState M q S z w role =
      ((cameraResolvedSeededClockAffineSixSourceRoleAnalyses M q S z w role).boundarySeed,
       cameraChannelAnalysisSynthesis S
        (cameraResolvedSeededClockAffineSixSourceRoleAnalyses M q S z w role).cameraAnalysis) := by
  apply Prod.ext
  · rw [cameraResolvedSeededClockAffineSixSourceRoleAnalyses_boundarySeed]
    simp [canonicalC3SixSourceAffineRoleState, canonicalOrdinaryBoundarySeed_eq_one]
  · exact (cameraResolvedSeededClockAffineSixSourceRoleAnalyses_synthesis_eq_role
      M q S z w role).symm

/-- Concrete audit of the original target: at cutoff zero its six gradient
analyses are zero. The global ordinary unit seed is not a field of that
homogeneous target. -/
theorem nativeC3SeededClockTfvdSixSourceAnalysis_zero_cutoff
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    nativeC3SeededClockTfvdSixSourceAnalysis 0 q S z w = 0 := by
  have ho (s : ℂ) : canonicalCompletedC3DirichletGradientPrefixState s 0 = 0 := by
    ext n
    simp
  have hl (s : ℂ) : canonicalCompletedC3LogJetPrefixState s 0 = 0 := by
    ext n
    simp
  simp [nativeC3SeededClockTfvdSixSourceAnalysis,
    nativeC3SeededClockOrdinaryTfvdAnalysis, nativeC3SeededClockLogJetTfvdAnalysis, ho, hl]

/-- The complete source still has its fixed seed at cutoff zero. -/
theorem canonicalC3SixSourceAffineRoleState_zero_cutoff
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    canonicalC3SixSourceAffineRoleState 0 q S z w = canonicalC3SixSourceFixedRoleSeed S := by
  rw [canonicalC3SixSourceAffineRoleState_eq_fixedSeed_add_variation,
    nativeC3SeededClockTfvdSixSourceAnalysis_zero_cutoff]
  have hroles : canonicalC3SixSourceRoleAnalysis S
      (0 : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) = 0 := by
    funext role
    rcases role with ⟨parameter, channel⟩
    cases parameter <;> cases channel <;> rfl
  rw [hroles, map_zero, add_zero]

/-- A homogeneous incidence map cannot carry the fixed canonical seed at
every input. This no-go concerns the complete seeded carrier only; the
existing gradient-analysis linear interface is not contradicted. -/
theorem no_homogeneous_incidence_map_realizes_fixed_ordinary_seed
    (S : Finset NativeGpreBoundaryContext)
    (L : (ℕ →₀ ℝ) →ₗ[ℝ] CanonicalC3AffineSixRoleAnalysisCarrier S) :
    ¬ ∀ x, (L x (.z, .ordinary)).1 = canonicalOrdinaryBoundarySeed 0 := by
  intro h
  have hz := h 0
  simp [canonicalOrdinaryBoundarySeed_eq_one] at hz

/-- The original homogeneous interface can remain the variation input. The
complete lift is affine assembly after its unchanged six-role view. -/
def canonicalC3SixSourceAffineIncidenceLiftOfVariation
    (S : Finset NativeGpreBoundaryContext)
    (variation : BR2IncidenceToCanonicalC3SixSourceAnalysis S) :
    (ℕ →₀ ℝ) →ᵃ[ℝ] CanonicalC3AffineSixRoleAnalysisCarrier S :=
  (canonicalC3SixSourceRoleAffineAssembly S).comp
    ((canonicalC3SixSourceRoleAnalysisLinearMap S).comp variation).toAffineMap

/-- The corrected interface retains the exact homogeneous analysis data at
every role, with no copies invented and no role relabeling. -/
theorem canonicalC3SixSourceAffineIncidenceLiftOfVariation_analysis
    (S : Finset NativeGpreBoundaryContext)
    (variation : BR2IncidenceToCanonicalC3SixSourceAnalysis S)
    (x : ℕ →₀ ℝ) (role : CanonicalC3SixSourceRole) :
    (canonicalC3SixSourceAffineIncidenceLiftOfVariation S variation x role).2 =
      canonicalC3SixSourceRoleAnalysis S (variation x) role := by
  exact canonicalC3SixSourceRoleAffineAssembly_analysis S _ role

/-- In particular, fixed seed insertion does not alter any native value
coordinate pairing of a given role variation. No actual BR2-to-role map is
asserted by this preservation identity. -/
theorem canonicalC3SixSourceAffineIncidenceLiftOfVariation_valuePairing
    (S : Finset NativeGpreBoundaryContext)
    (variation : BR2IncidenceToCanonicalC3SixSourceAnalysis S)
    (x y : ℕ →₀ ℝ) (role : CanonicalC3SixSourceRole) (c : ↥S) :
    inner ℂ
      ((canonicalC3SixSourceAffineIncidenceLiftOfVariation S variation x role).2.2.1 c)
      ((canonicalC3SixSourceAffineIncidenceLiftOfVariation S variation y role).2.2.1 c) =
    inner ℂ ((canonicalC3SixSourceRoleAnalysis S (variation x) role).2.1 c)
      ((canonicalC3SixSourceRoleAnalysis S (variation y) role).2.1 c) := by
  rw [canonicalC3SixSourceAffineIncidenceLiftOfVariation_analysis,
    canonicalC3SixSourceAffineIncidenceLiftOfVariation_analysis]

end

end CarrySelfAdjointOperator

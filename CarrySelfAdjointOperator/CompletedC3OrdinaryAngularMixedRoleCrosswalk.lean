import CarrySelfAdjointOperator.CompletedC3PolarizedCameraCrossResidual
import CPFormal.Analytic.CpFiniteGenuineAngularGreenBudget
import CPFormal.Analytic.CpFiniteScalarSynthesisSummationByParts

/-!
# The historical ordinary angular correction in the current mixed carrier

Read the original weights 1,2,0 from the retained ordinary prefixes. The
log-jet and other source coordinates remain in the input carrier. These are
observations, not a lossless replacement of that carrier. A finite-support
probe tests whether the historical ordinary correction can be identified
with the current mixed ordinary/log-jet Green provenance on all sources.
-/
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary
open scoped ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false

/-- Historical angular block, read from a vector with the original weights. -/
def canonicalC3OrdinaryAngularBlockReadout (g : CarryVerticalL2) (m : ℕ) : ℂ :=
  -(g (3 * m) + 2 * g (3 * m + 1))

/-- All local cross terms, including the restored dormant third edge. -/
def canonicalC3OrdinaryAngularLocalCorrectionReadout
    (M : ℕ) (x : CanonicalC3AllCutoffMixedSourceHilbert) : ℂ :=
  let g := x.wSource.1
  let h := x.reflectedZSource.1
  ∑ m ∈ Finset.range M,
    (2 * conj (g (3 * m)) * h (3 * m + 1) +
    2 * conj (g (3 * m + 1)) * h (3 * m) +
    3 * conj (g (3 * m + 1)) * h (3 * m + 1) -
    conj (g (3 * m + 2)) * h (3 * m + 2))

/-- Ordered interblock terms reuse the existing full port ledger. -/
def canonicalC3OrdinaryAngularOffDiagonalReadout
    (M : ℕ) (x : CanonicalC3AllCutoffMixedSourceHilbert) : ℂ :=
  finiteOffDiagonalPortWronskian M (fun _ => 0)
    (canonicalC3OrdinaryAngularBlockReadout x.wSource.1)
    (canonicalC3OrdinaryAngularBlockReadout x.reflectedZSource.1) (fun _ => 0)

/-- Scalar product is formed after each complete finite angular synthesis. -/
def canonicalC3OrdinaryAngularScalarReadout
    (M : ℕ) (x : CanonicalC3AllCutoffMixedSourceHilbert) : ℂ :=
  finiteScalarPortWronskian M (fun _ => 0)
    (canonicalC3OrdinaryAngularBlockReadout x.wSource.1)
    (canonicalC3OrdinaryAngularBlockReadout x.reflectedZSource.1) (fun _ => 0)

/-- Exact indices: current prefixes and historical angular blocks use the
same consecutive material edges 3m and 3m+1, not C2 vertical depths. -/
theorem canonicalC3OrdinaryAngularBlockReadout_prefix
    (M : ℕ) (s : ℂ) {m : ℕ} (hm : m < M) :
    canonicalC3OrdinaryAngularBlockReadout
        (canonicalCompletedC3DirichletGradientPrefixState s (3 * M)) m =
      canonicalAngularGradientBlock m s := by
  rw [canonicalAngularGradientBlock_eq_two_edges]
  unfold canonicalC3OrdinaryAngularBlockReadout
  rw [canonicalCompletedC3DirichletGradientPrefixState_apply,
    canonicalCompletedC3DirichletGradientPrefixState_apply,
    if_pos (by omega), if_pos (by omega)]

/-- The old local correction is literally an observation of the retained
ordinary coordinates of the current canonical mixed prefix. -/
theorem canonicalC3OrdinaryAngularLocalCorrectionReadout_prefix_eq_historical
    (M : ℕ) (s : ℂ) :
    canonicalC3OrdinaryAngularLocalCorrectionReadout M
        (canonicalC3AllCutoffMixedSourcePrefixState M s s) =
      finiteCanonicalAngularLocalGreenCorrection M s := by
  unfold canonicalC3OrdinaryAngularLocalCorrectionReadout
    finiteCanonicalAngularLocalGreenCorrection
  apply Finset.sum_congr rfl
  intro m hm
  have h0 : 3 * m < 3 * M := by have := Finset.mem_range.mp hm; omega
  have h1 : 3 * m + 1 < 3 * M := by have := Finset.mem_range.mp hm; omega
  have h2 : 3 * m + 2 < 3 * M := by have := Finset.mem_range.mp hm; omega
  simp only [canonicalC3AllCutoffMixedSourcePrefixState_wSource,
    canonicalC3AllCutoffMixedSourcePrefixState_reflectedZSource,
    canonicalCompletedC3HilbertPrefixState,
    canonicalCompletedC3DirichletGradientPrefixState_apply,
    if_pos h0, if_pos h1, if_pos h2, canonicalAngularLocalGreenCorrection]

/-- The historical interblock correction is retained with every ordered pair. -/
theorem canonicalC3OrdinaryAngularOffDiagonalReadout_prefix_eq_historical
    (M : ℕ) (s : ℂ) :
    canonicalC3OrdinaryAngularOffDiagonalReadout M
        (canonicalC3AllCutoffMixedSourcePrefixState M s s) =
      finiteCanonicalAngularPairingOffDiagonal M s := by
  unfold canonicalC3OrdinaryAngularOffDiagonalReadout
    finiteCanonicalAngularPairingOffDiagonal finiteOffDiagonalPortWronskian
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  simp only [canonicalC3AllCutoffMixedSourcePrefixState_wSource,
    canonicalC3AllCutoffMixedSourcePrefixState_reflectedZSource,
    canonicalCompletedC3HilbertPrefixState, finitePortWedgeEntry,
    canonicalC3OrdinaryAngularBlockReadout_prefix M s (Finset.mem_range.mp hm),
    canonicalC3OrdinaryAngularBlockReadout_prefix M (reflectedParameter s) (Finset.mem_range.mp hn)]

/-- The old scalar observation, not a new moment source or metric. -/
theorem canonicalC3OrdinaryAngularScalarReadout_prefix_eq_historical
    (M : ℕ) (s : ℂ) :
    canonicalC3OrdinaryAngularScalarReadout M
        (canonicalC3AllCutoffMixedSourcePrefixState M s s) =
      finiteCanonicalAngularScalarPairing M s := by
  unfold canonicalC3OrdinaryAngularScalarReadout
    finiteCanonicalAngularScalarPairing finiteScalarPortWronskian finitePortSynthesis
  have hg : (∑ m ∈ Finset.range M, canonicalC3OrdinaryAngularBlockReadout
      (canonicalC3AllCutoffMixedSourcePrefixState M s s).wSource.1 m) =
      ∑ m ∈ Finset.range M, canonicalAngularGradientBlock m s := by
    apply Finset.sum_congr rfl
    intro m hm
    exact canonicalC3OrdinaryAngularBlockReadout_prefix M s (Finset.mem_range.mp hm)
  have hh : (∑ m ∈ Finset.range M, canonicalC3OrdinaryAngularBlockReadout
      (canonicalC3AllCutoffMixedSourcePrefixState M s s).reflectedZSource.1 m) =
      ∑ m ∈ Finset.range M, canonicalAngularGradientBlock m (reflectedParameter s) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact canonicalC3OrdinaryAngularBlockReadout_prefix M (reflectedParameter s)
      (Finset.mem_range.mp hm)
  rw [hg, hh]

/-- The complete historical ledger now lives on the same ordinary prefix
vectors as the current finite Green port. This is not the mixed log-jet form. -/
theorem canonicalC3OrdinaryAngularPrefix_ledger
    (M : ℕ) (s : ℂ) :
    canonicalC3OrdinaryAngularScalarReadout M
        (canonicalC3AllCutoffMixedSourcePrefixState M s s) =
      inner ℂ (canonicalCompletedC3DirichletGradientPrefixState s (3 * M))
        (canonicalCompletedC3DirichletGradientPrefixState (reflectedParameter s) (3 * M)) +
      canonicalC3OrdinaryAngularLocalCorrectionReadout M
        (canonicalC3AllCutoffMixedSourcePrefixState M s s) +
      canonicalC3OrdinaryAngularOffDiagonalReadout M
        (canonicalC3AllCutoffMixedSourcePrefixState M s s) := by
  rw [canonicalC3OrdinaryAngularScalarReadout_prefix_eq_historical,
    canonicalC3OrdinaryAngularLocalCorrectionReadout_prefix_eq_historical,
    canonicalC3OrdinaryAngularOffDiagonalReadout_prefix_eq_historical,
    ← finiteReflectedGradientPairing_eq_inner_completedC3Prefixes,
    finiteCanonicalAngularScalarPairing_eq_green_add_correction]
  unfold finiteCanonicalAngularGreenCorrection
  ring

/-- The historical corrected ordinary pairing reaches the current bracket
Green readout through its existing radial coefficient, not by identifying
an ordinary Gram with a log-jet wedge. -/
theorem canonicalC3BracketGreenReadout_eq_radial_mul_correctedAngular
    (M : ℕ) (s : ℂ) :
    canonicalC3BracketTfvdMixedGreenReadout M s s =
      ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        (canonicalC3OrdinaryAngularScalarReadout M
            (canonicalC3AllCutoffMixedSourcePrefixState M s s) -
          canonicalC3OrdinaryAngularLocalCorrectionReadout M
            (canonicalC3AllCutoffMixedSourcePrefixState M s s) -
          canonicalC3OrdinaryAngularOffDiagonalReadout M
            (canonicalC3AllCutoffMixedSourcePrefixState M s s)) := by
  rw [canonicalC3BracketTfvdMixedGreenReadout_eq_bracketGreen]
  rw [Nat.mul_comm M 3, greenForm_finiteC3GenuineBracket_eq_coefficient_mul_prefixGram]
  rw [canonicalC3OrdinaryAngularPrefix_ledger]
  ring

/-- Finite-support role probe: the ordinary coordinates are fixed while
only the z-source log-jet coordinate at material edge 1 varies. -/
def canonicalC3AngularLogRoleProbe (a : ℂ) : CanonicalC3AllCutoffMixedSourceHilbert :=
  WithLp.toLp 2 ((0, lp.single 2 1 a),
    WithLp.toLp 2 ((lp.single 2 0 (1 : ℂ), 0), (0, 0)))

/-- Every historical ordinary correction remains zero on the role probe. -/
theorem canonicalC3OrdinaryAngularRoleProbe_corrections_zero (a : ℂ) :
    canonicalC3OrdinaryAngularLocalCorrectionReadout 1 (canonicalC3AngularLogRoleProbe a) = 0 ∧
    canonicalC3OrdinaryAngularOffDiagonalReadout 1 (canonicalC3AngularLogRoleProbe a) = 0 := by
  simp [canonicalC3OrdinaryAngularLocalCorrectionReadout,
    canonicalC3OrdinaryAngularOffDiagonalReadout, canonicalC3AngularLogRoleProbe,
    CanonicalC3AllCutoffMixedSourceHilbert.wSource,
    CanonicalC3AllCutoffMixedSourceHilbert.reflectedZSource,
    canonicalC3OrdinaryAngularBlockReadout, finiteOffDiagonalPortWronskian,
    finitePortWedgeEntry]

/-- The actual mixed ordinary/log-jet provenance sees that independent role.
The Green leg paired with the zero reflected source contributes zero. -/
theorem canonicalC3AngularLogRoleProbe_mixedProvenance (a : ℂ) :
    CanonicalC3AllCutoffMixedSourceHilbert.greenProvenanceReadout 1 0 0
      (canonicalC3AngularLogRoleProbe a) = -a := by
  have hz : (WithLp.toLp 2 (fun _ : Fin 3 => (0 : ℂ)) :
      NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3) = 0 := rfl
  have hcases (x : ℂ) (f : Fin 1 → ℂ) : Fin.cases x f (1 : Fin 2) = f 0 := rfl
  simp [CanonicalC3AllCutoffMixedSourceHilbert.greenProvenanceReadout,
    CanonicalC3AllCutoffMixedSourceHilbert.mixedLegs,
    CanonicalC3AllCutoffMixedSourceHilbert.greenPort,
    CanonicalC3AllCutoffMixedSourceHilbert.zSource,
    CanonicalC3AllCutoffMixedSourceHilbert.wSource,
    CanonicalC3AllCutoffMixedSourceHilbert.reflectedZSource,
    canonicalC3AngularLogRoleProbe, sameSEdgeBoundaryWedge, greenForm,
    Fintype.sum_prod_type, Fin.sum_univ_two,
    hcases, hz,
    lp.single_apply]

/-- Local no-go on the full mixed carrier. An ordinary-only observation
cannot be substituted for the current Green provenance on arbitrary states.
This does not refute a separate transport on the canonical orbit. -/
theorem not_ordinaryAngularCorrection_eq_mixedGreenProvenance_on_all_sources :
    ¬ ∀ x : CanonicalC3AllCutoffMixedSourceHilbert,
      canonicalC3OrdinaryAngularLocalCorrectionReadout 1 x +
          canonicalC3OrdinaryAngularOffDiagonalReadout 1 x =
        CanonicalC3AllCutoffMixedSourceHilbert.greenProvenanceReadout 1 0 0 x := by
  intro h
  have hw := h (canonicalC3AngularLogRoleProbe 1)
  rcases canonicalC3OrdinaryAngularRoleProbe_corrections_zero 1 with ⟨hl, ho⟩
  rw [hl, ho, canonicalC3AngularLogRoleProbe_mixedProvenance] at hw
  norm_num at hw

end
end CarrySelfAdjointOperator

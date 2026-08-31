import CarrySelfAdjointOperator.CompletedNativeCompletedChiralEnergyLedger
import Mathlib.Tactic

/-!
# Native causal-cell chiral ledger

The atom ledger retains the seed and each coefficient 1, -2, 1 of a C3
bracket as separate provenance.  This is exact, but its positive atomwise
local part is not the geometrically completed center--leg cell.

This module regroups those atoms without changing their scalar synthesis.
The new provenance type has one seed and one entry for each complete C3 cell.
Each cell entry is definitionally assembled from its three old atoms and is
then identified with the existing bracket and log-bracket block.

The resulting theorem separates within-cell compensation from cross-cell
provenance.  No sign, zero-set, Stieltjes, Jacobi, or confinement premise is
introduced.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Provenance after grouping the three atoms of each complete C3 bracket
cell.  The finite seed remains an independent block. -/
abbrev CanonicalC3FiniteDirichletCell (M : ℕ) := Unit ⊕ Fin M

/-- Value carried by a grouped C3 cell. -/
def canonicalC3FiniteDirichletCellValue
    (M : ℕ) (s : ℂ) : CanonicalC3FiniteDirichletCell M → ℂ
  | Sum.inl seed =>
      canonicalC3FiniteDirichletValueAtom M s (Sum.inl seed)
  | Sum.inr m =>
      ∑ r : Fin 3,
        canonicalC3FiniteDirichletValueAtom M s (Sum.inr (m, r))

/-- Log jet carried by the same grouped C3 cell. -/
def canonicalC3FiniteDirichletCellLogJet
    (M : ℕ) (s : ℂ) : CanonicalC3FiniteDirichletCell M → ℂ
  | Sum.inl seed =>
      canonicalC3FiniteDirichletLogJetAtom M s (Sum.inl seed)
  | Sum.inr m =>
      ∑ r : Fin 3,
        canonicalC3FiniteDirichletLogJetAtom M s (Sum.inr (m, r))

/-- Height companion of one grouped cell.  The quarter turn is applied only
after all three center--leg atoms have been assembled. -/
def canonicalC3FiniteDirichletCellHeightCompanion
    (M : ℕ) (s : ℂ) (cell : CanonicalC3FiniteDirichletCell M) : ℂ :=
  Complex.I * canonicalC3FiniteDirichletCellLogJet M s cell

@[simp] theorem canonicalC3FiniteDirichletCellValue_seed
    (M : ℕ) (s : ℂ) (seed : Unit) :
    canonicalC3FiniteDirichletCellValue M s (Sum.inl seed) = 1 := by
  simp [canonicalC3FiniteDirichletCellValue,
    canonicalC3FiniteDirichletValueAtom,
    canonicalC3FiniteDirichletAtomWeight,
    canonicalC3FiniteDirichletAtomIndex, natDirichletTerm, dirichletTerm]

@[simp] theorem canonicalC3FiniteDirichletCellLogJet_seed
    (M : ℕ) (s : ℂ) (seed : Unit) :
    canonicalC3FiniteDirichletCellLogJet M s (Sum.inl seed) = 0 := by
  simp [canonicalC3FiniteDirichletCellLogJet,
    canonicalC3FiniteDirichletLogJetAtom,
    canonicalC3FiniteDirichletAtomWeight,
    canonicalC3FiniteDirichletAtomIndex, natLogDirichletTerm]

@[simp] theorem canonicalC3FiniteDirichletCellHeightCompanion_seed
    (M : ℕ) (s : ℂ) (seed : Unit) :
    canonicalC3FiniteDirichletCellHeightCompanion M s (Sum.inl seed) = 0 := by
  simp [canonicalC3FiniteDirichletCellHeightCompanion]

/-- A grouped value cell is exactly the genuine C3 bracket. -/
theorem canonicalC3FiniteDirichletCellValue_cell
    {M : ℕ} (m : Fin M) (s : ℂ) :
    canonicalC3FiniteDirichletCellValue M s (Sum.inr m) =
      realCpSaturatedBracket 3 m s := by
  exact canonicalC3FiniteDirichletValueAtom_cellSum m s

/-- A grouped log-jet cell is exactly the canonical log bracket. -/
theorem canonicalC3FiniteDirichletCellLogJet_cell
    {M : ℕ} (m : Fin M) (s : ℂ) :
    canonicalC3FiniteDirichletCellLogJet M s (Sum.inr m) =
      canonicalLogBracketBlock m s := by
  exact canonicalC3FiniteDirichletLogJetAtom_cellSum m s

/-- The grouped height companion is the quarter-turned log bracket. -/
theorem canonicalC3FiniteDirichletCellHeightCompanion_cell
    {M : ℕ} (m : Fin M) (s : ℂ) :
    canonicalC3FiniteDirichletCellHeightCompanion M s (Sum.inr m) =
      Complex.I * canonicalLogBracketBlock m s := by
  rw [canonicalC3FiniteDirichletCellHeightCompanion,
    canonicalC3FiniteDirichletCellLogJet_cell]

/-- Regrouping does not alter the synthesized finite value chart. -/
theorem canonicalC3FiniteDirichletCellValue_sum_eq_valueChart
    (M : ℕ) (s : ℂ) :
    ∑ cell : CanonicalC3FiniteDirichletCell M,
        canonicalC3FiniteDirichletCellValue M s cell =
      finiteBracketedDirichletChart 3 M s := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [canonicalC3FiniteDirichletCellValue_seed,
    canonicalC3FiniteDirichletCellValue_cell]
  rw [show (∑ _seed : Unit, (1 : ℂ)) = 1 by simp]
  unfold finiteBracketedDirichletChart
  rw [seedSum_three_dirichlet_eq_one]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun m : ℕ => realCpSaturatedBracket 3 m s) M

/-- Regrouping does not alter the synthesized finite log-jet chart. -/
theorem canonicalC3FiniteDirichletCellLogJet_sum_eq_logJetChart
    (M : ℕ) (s : ℂ) :
    ∑ cell : CanonicalC3FiniteDirichletCell M,
        canonicalC3FiniteDirichletCellLogJet M s cell =
      finiteCanonicalLogBracketChart M s := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [canonicalC3FiniteDirichletCellLogJet_seed,
    canonicalC3FiniteDirichletCellLogJet_cell, Finset.sum_const_zero,
    zero_add]
  unfold finiteCanonicalLogBracketChart
  exact Fin.sum_univ_eq_sum_range
    (fun m : ℕ => canonicalLogBracketBlock m s) M

/-- Regrouping also preserves the complete height companion. -/
theorem canonicalC3FiniteDirichletCellHeightCompanion_sum_eq
    (M : ℕ) (s : ℂ) :
    ∑ cell : CanonicalC3FiniteDirichletCell M,
        canonicalC3FiniteDirichletCellHeightCompanion M s cell =
      Complex.I * finiteCanonicalLogBracketChart M s := by
  unfold canonicalC3FiniteDirichletCellHeightCompanion
  rw [← Finset.mul_sum,
    canonicalC3FiniteDirichletCellLogJet_sum_eq_logJetChart]

/-- Sum of the diagonal wedges after complete center--leg cells have been
assembled.  This object is intentionally signed. -/
def canonicalC3FiniteDirichletCellLocalHeightReadout
    (M : ℕ) (s : ℂ) : ℝ :=
  ∑ cell : CanonicalC3FiniteDirichletCell M,
    (scalarBoundaryWedge
      (canonicalC3FiniteDirichletCellValue M s cell)
      (canonicalC3FiniteDirichletCellHeightCompanion M s cell)).im

/-- Ordered provenance between complete cells, including all seed--cell
pairings. -/
def canonicalC3FiniteDirichletInterCellHeightCross
    (M : ℕ) (s : ℂ) : ℝ :=
  (scalarBoundaryCrossProvenance
    (canonicalC3FiniteDirichletCellValue M s)
    (canonicalC3FiniteDirichletCellHeightCompanion M s)).im

/-- Cross provenance internal to each complete center--leg cell.  This is the
part of the atomwise cross ledger absorbed before distinct cells interact. -/
def canonicalC3FiniteDirichletWithinCellHeightCross
    (M : ℕ) (s : ℂ) : ℝ :=
  ∑ m : Fin M,
    (scalarBoundaryCrossProvenance
      (fun r : Fin 3 =>
        canonicalC3FiniteDirichletValueAtom M s (Sum.inr (m, r)))
      (fun r : Fin 3 =>
        canonicalC3FiniteDirichletHeightCompanionAtom M s
          (Sum.inr (m, r)))).im

/-- The old positive atom energy is literally the sum of the diagonal atom
wedges. -/
theorem canonicalC3FiniteDirichletLocalHeightEnergy_eq_sum_atomWedges
    (M : ℕ) (s : ℂ) :
    canonicalC3FiniteDirichletLocalHeightEnergy M s =
      ∑ atom : CanonicalC3FiniteDirichletAtom M,
        (scalarBoundaryWedge
          (canonicalC3FiniteDirichletValueAtom M s atom)
          (canonicalC3FiniteDirichletHeightCompanionAtom M s atom)).im := by
  unfold canonicalC3FiniteDirichletLocalHeightEnergy
  apply Finset.sum_congr rfl
  intro atom hatom
  exact (canonicalC3FiniteDirichletAtom_heightWedge_im M s atom).symm

/-- The seed has zero local height wedge, so the atom energy is the iterated
sum over the three atoms of every complete cell. -/
theorem canonicalC3FiniteDirichletLocalHeightEnergy_eq_sum_cellAtoms
    (M : ℕ) (s : ℂ) :
    canonicalC3FiniteDirichletLocalHeightEnergy M s =
      ∑ m : Fin M, ∑ r : Fin 3,
        (scalarBoundaryWedge
          (canonicalC3FiniteDirichletValueAtom M s (Sum.inr (m, r)))
          (canonicalC3FiniteDirichletHeightCompanionAtom M s
            (Sum.inr (m, r)))).im := by
  rw [canonicalC3FiniteDirichletLocalHeightEnergy_eq_sum_atomWedges,
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hseed :
      (∑ seed : Unit,
        (scalarBoundaryWedge
          (canonicalC3FiniteDirichletValueAtom M s (Sum.inl seed))
          (canonicalC3FiniteDirichletHeightCompanionAtom M s
            (Sum.inl seed))).im) = 0 := by
    apply Finset.sum_eq_zero
    intro seed hseed
    rw [canonicalC3FiniteDirichletAtom_heightWedge_im]
    simp [canonicalC3FiniteDirichletAtomIndex]
  rw [hseed, zero_add]

/-- One completed center--leg cell consists of its three atom wedges plus the
complete within-cell cross provenance. -/
theorem canonicalC3FiniteDirichletCell_localWedge_im
    {M : ℕ} (m : Fin M) (s : ℂ) :
    (scalarBoundaryWedge
        (canonicalC3FiniteDirichletCellValue M s (Sum.inr m))
        (canonicalC3FiniteDirichletCellHeightCompanion M s
          (Sum.inr m))).im =
      (∑ r : Fin 3,
        (scalarBoundaryWedge
          (canonicalC3FiniteDirichletValueAtom M s (Sum.inr (m, r)))
          (canonicalC3FiniteDirichletHeightCompanionAtom M s
            (Sum.inr (m, r)))).im) +
        (scalarBoundaryCrossProvenance
          (fun r : Fin 3 =>
            canonicalC3FiniteDirichletValueAtom M s (Sum.inr (m, r)))
          (fun r : Fin 3 =>
            canonicalC3FiniteDirichletHeightCompanionAtom M s
              (Sum.inr (m, r)))).im := by
  have hheight :
      (∑ r : Fin 3,
        canonicalC3FiniteDirichletHeightCompanionAtom M s
          (Sum.inr (m, r))) =
        canonicalC3FiniteDirichletCellHeightCompanion M s (Sum.inr m) := by
    unfold canonicalC3FiniteDirichletHeightCompanionAtom
      canonicalC3FiniteDirichletCellHeightCompanion
      canonicalC3FiniteDirichletCellLogJet
    rw [← Finset.mul_sum]
  have h := congrArg Complex.im
    (scalarBoundaryWedge_sum_eq_local_add_crossProvenance
      (fun r : Fin 3 =>
        canonicalC3FiniteDirichletValueAtom M s (Sum.inr (m, r)))
      (fun r : Fin 3 =>
        canonicalC3FiniteDirichletHeightCompanionAtom M s
          (Sum.inr (m, r))))
  rw [show (∑ r : Fin 3,
      canonicalC3FiniteDirichletValueAtom M s (Sum.inr (m, r))) =
        canonicalC3FiniteDirichletCellValue M s (Sum.inr m) by rfl,
    hheight, Complex.add_im, Complex.im_sum] at h
  exact h

/-- Cellular regrouping absorbs exactly the within-cell cross provenance into
the signed local cell readout. -/
theorem canonicalC3FiniteDirichletCellLocalHeightReadout_eq_atomLocal_add_within
    (M : ℕ) (s : ℂ) :
    canonicalC3FiniteDirichletCellLocalHeightReadout M s =
      canonicalC3FiniteDirichletLocalHeightEnergy M s +
        canonicalC3FiniteDirichletWithinCellHeightCross M s := by
  unfold canonicalC3FiniteDirichletCellLocalHeightReadout
    canonicalC3FiniteDirichletWithinCellHeightCross
  rw [Fintype.sum_sum_type]
  have hseed :
      (∑ seed : Unit,
        (scalarBoundaryWedge
          (canonicalC3FiniteDirichletCellValue M s (Sum.inl seed))
          (canonicalC3FiniteDirichletCellHeightCompanion M s
            (Sum.inl seed))).im) = 0 := by simp [scalarBoundaryWedge]
  rw [hseed, zero_add]
  simp_rw [canonicalC3FiniteDirichletCell_localWedge_im]
  rw [Finset.sum_add_distrib,
    canonicalC3FiniteDirichletLocalHeightEnergy_eq_sum_cellAtoms]

/-- Exact center--leg regrouping of the finite height boundary. -/
theorem finiteC3HeightBoundaryWedge_im_eq_cellLocal_add_interCellCross
    (M : ℕ) (s : ℂ) :
    (scalarBoundaryWedge
        (finiteBracketedDirichletChart 3 M s)
        (Complex.I * finiteCanonicalLogBracketChart M s)).im =
      canonicalC3FiniteDirichletCellLocalHeightReadout M s +
        canonicalC3FiniteDirichletInterCellHeightCross M s := by
  rw [← canonicalC3FiniteDirichletCellValue_sum_eq_valueChart,
    ← canonicalC3FiniteDirichletCellHeightCompanion_sum_eq,
    scalarBoundaryWedge_sum_eq_local_add_crossProvenance,
    Complex.add_im]
  unfold canonicalC3FiniteDirichletCellLocalHeightReadout
    canonicalC3FiniteDirichletInterCellHeightCross
  rw [Complex.im_sum]

/-- The atom and causal-cell ledgers are two exact provenance resolutions of
the same scalar boundary.  In particular, all within-cell compensation is
retained when the three atoms are regrouped. -/
theorem canonicalC3FiniteAtomLedger_eq_cellLedger
    (M : ℕ) (s : ℂ) :
    canonicalC3FiniteDirichletLocalHeightEnergy M s +
        (scalarBoundaryCrossProvenance
          (canonicalC3FiniteDirichletValueAtom M s)
          (canonicalC3FiniteDirichletHeightCompanionAtom M s)).im =
      canonicalC3FiniteDirichletCellLocalHeightReadout M s +
        canonicalC3FiniteDirichletInterCellHeightCross M s := by
  rw [← finiteC3HeightBoundaryWedge_im_eq_localEnergy_add_crossProvenance,
    ← finiteC3HeightBoundaryWedge_im_eq_cellLocal_add_interCellCross]

/-- Exact provenance refinement: atomwise cross terms split into compensation
inside each complete bracket cell and provenance between distinct cells. -/
theorem canonicalC3FiniteDirichletAtomCross_eq_within_add_interCell
    (M : ℕ) (s : ℂ) :
    (scalarBoundaryCrossProvenance
        (canonicalC3FiniteDirichletValueAtom M s)
        (canonicalC3FiniteDirichletHeightCompanionAtom M s)).im =
      canonicalC3FiniteDirichletWithinCellHeightCross M s +
        canonicalC3FiniteDirichletInterCellHeightCross M s := by
  have hledger := canonicalC3FiniteAtomLedger_eq_cellLedger M s
  rw [
    canonicalC3FiniteDirichletCellLocalHeightReadout_eq_atomLocal_add_within]
    at hledger
  linarith

/-! ## Stable cell-local limit -/

/-- One signed local height term after the complete C3 bracket has been
assembled. -/
def canonicalC3DirichletCellHeightTerm (m : ℕ) (s : ℂ) : ℝ :=
  (scalarBoundaryWedge
    (realCpSaturatedBracket 3 m s)
    (Complex.I * canonicalLogBracketBlock m s)).im

/-- Absolute summability of the canonical log-bracket blocks. -/
theorem summable_norm_canonicalLogBracketBlock
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun m : ℕ => ‖canonicalLogBracketBlock m s‖) := by
  have hgradient := summable_norm_positiveLogDirichletGradient hs
  have hleft := hgradient.comp_injective
    (show Function.Injective (fun m : ℕ => 3 * m + 1) by
      intro a b hab
      exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel hab))
  have hright := hgradient.comp_injective
    (show Function.Injective (fun m : ℕ => 3 * m + 2) by
      intro a b hab
      exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel hab))
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    (hright.add hleft)
  have hblock :
      canonicalLogBracketBlock m s =
        positiveLogDirichletGradient s (3 * m + 2) -
          positiveLogDirichletGradient s (3 * m + 1) := by
    simp [canonicalLogBracketBlock, positiveLogDirichletGradient]
    ring
  rw [hblock]
  exact norm_sub_le _ _

/-- The scalar boundary wedge of a complete bracket and its height companion
is bounded by twice the product of their norms. -/
theorem norm_scalarBoundaryWedge_bracket_heightCompanion_le
    (m : ℕ) (s : ℂ) :
    ‖scalarBoundaryWedge
        (realCpSaturatedBracket 3 m s)
        (Complex.I * canonicalLogBracketBlock m s)‖ ≤
      2 * ‖realCpSaturatedBracket 3 m s‖ *
        ‖canonicalLogBracketBlock m s‖ := by
  unfold scalarBoundaryWedge
  calc
    ‖(starRingEnd ℂ) (realCpSaturatedBracket 3 m s) *
          (Complex.I * canonicalLogBracketBlock m s) -
        (starRingEnd ℂ) (Complex.I * canonicalLogBracketBlock m s) *
          realCpSaturatedBracket 3 m s‖
        ≤
      ‖(starRingEnd ℂ) (realCpSaturatedBracket 3 m s) *
          (Complex.I * canonicalLogBracketBlock m s)‖ +
        ‖(starRingEnd ℂ) (Complex.I * canonicalLogBracketBlock m s) *
          realCpSaturatedBracket 3 m s‖ := norm_sub_le _ _
    _ = 2 * ‖realCpSaturatedBracket 3 m s‖ *
          ‖canonicalLogBracketBlock m s‖ := by
      simp
      ring

/-- Complete center--leg grouping makes the signed local-height series
absolutely summable throughout the open native strip. -/
theorem summable_canonicalC3DirichletCellHeightTerm
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun m : ℕ => canonicalC3DirichletCellHeightTerm m s) := by
  have hvalue :
      Summable (fun m : ℕ => ‖realCpSaturatedBracket 3 m s‖) :=
    summable_norm_realCpSaturatedBracket 3 (by norm_num) (by linarith)
  have hlog :
      Summable (fun m : ℕ => ‖canonicalLogBracketBlock m s‖) :=
    summable_norm_canonicalLogBracketBlock hs
  have hproduct :
      Summable (fun pair : ℕ × ℕ =>
        ‖realCpSaturatedBracket 3 pair.1 s‖ *
          ‖canonicalLogBracketBlock pair.2 s‖) :=
    hvalue.mul_of_nonneg hlog
      (fun m => norm_nonneg _) (fun m => norm_nonneg _)
  have hdiagonal :
      Summable (fun m : ℕ =>
        ‖realCpSaturatedBracket 3 m s‖ *
          ‖canonicalLogBracketBlock m s‖) := by
    have hdiagInjective :
        Function.Injective (fun m : ℕ => (m, m)) := by
      intro a b hab
      exact congrArg Prod.fst hab
    simpa [Function.comp_def] using
      hproduct.comp_injective hdiagInjective
  have hmajorant :
      Summable (fun m : ℕ =>
        2 * (‖realCpSaturatedBracket 3 m s‖ *
          ‖canonicalLogBracketBlock m s‖)) :=
    hdiagonal.mul_left 2
  refine Summable.of_norm_bounded hmajorant (fun m => ?_)
  unfold canonicalC3DirichletCellHeightTerm
  calc
    ‖(scalarBoundaryWedge
        (realCpSaturatedBracket 3 m s)
        (Complex.I * canonicalLogBracketBlock m s)).im‖
        = |(scalarBoundaryWedge
            (realCpSaturatedBracket 3 m s)
            (Complex.I * canonicalLogBracketBlock m s)).im| := Real.norm_eq_abs _
    _ ≤ ‖scalarBoundaryWedge
          (realCpSaturatedBracket 3 m s)
          (Complex.I * canonicalLogBracketBlock m s)‖ :=
      Complex.abs_im_le_norm _
    _ ≤ 2 * ‖realCpSaturatedBracket 3 m s‖ *
          ‖canonicalLogBracketBlock m s‖ :=
      norm_scalarBoundaryWedge_bracket_heightCompanion_le m s
    _ = 2 * (‖realCpSaturatedBracket 3 m s‖ *
          ‖canonicalLogBracketBlock m s‖) := by ring

/-- The finite grouped local readout is exactly the ordinary prefix of the
stable cell-height series. -/
theorem canonicalC3FiniteDirichletCellLocalHeightReadout_eq_sum_range
    (M : ℕ) (s : ℂ) :
    canonicalC3FiniteDirichletCellLocalHeightReadout M s =
      ∑ m ∈ Finset.range M, canonicalC3DirichletCellHeightTerm m s := by
  unfold canonicalC3FiniteDirichletCellLocalHeightReadout
  rw [Fintype.sum_sum_type]
  have hseed :
      (∑ seed : Unit,
        (scalarBoundaryWedge
          (canonicalC3FiniteDirichletCellValue M s (Sum.inl seed))
          (canonicalC3FiniteDirichletCellHeightCompanion M s
            (Sum.inl seed))).im) = 0 := by simp [scalarBoundaryWedge]
  rw [hseed, zero_add]
  simp_rw [canonicalC3FiniteDirichletCellValue_cell,
    canonicalC3FiniteDirichletCellHeightCompanion_cell]
  exact Fin.sum_univ_eq_sum_range
    (fun m : ℕ => canonicalC3DirichletCellHeightTerm m s) M

/-- The geometrically grouped local ledger has a genuine finite real limit. -/
theorem canonicalC3FiniteDirichletCellLocalHeightReadout_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun M : ℕ => canonicalC3FiniteDirichletCellLocalHeightReadout M s)
      Filter.atTop
      (nhds (∑' m : ℕ, canonicalC3DirichletCellHeightTerm m s)) := by
  have hsum := (summable_canonicalC3DirichletCellHeightTerm hs).tendsto_sum_tsum_nat
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun M =>
    (canonicalC3FiniteDirichletCellLocalHeightReadout_eq_sum_range M s).symm

/-- The synthesized finite height boundary converges before any provenance
split is chosen. -/
theorem finiteC3HeightBoundaryWedge_im_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun M : ℕ =>
        (scalarBoundaryWedge
          (finiteBracketedDirichletChart 3 M s)
          (Complex.I * finiteCanonicalLogBracketChart M s)).im)
      Filter.atTop
      (nhds
        (scalarBoundaryWedge
          (bracketedDirichletChart 3 s)
          (Complex.I *
            canonicalCompletedC3EnrichedTfvdLogJetTailReadout s)).im) := by
  have hledger :=
    canonicalC3FiniteHeightEnergyLedger_tendsto_rawHeightBoundaryWedge hs
  apply hledger.congr'
  exact Filter.Eventually.of_forall fun M =>
    (finiteC3HeightBoundaryWedge_im_eq_localEnergy_add_crossProvenance
      M s).symm

/-- Once complete cells are assembled, the remaining inter-cell provenance
also has a finite limit.  Its limit is the global boundary minus the stable
cell-local series, with no independent defect parameter. -/
theorem canonicalC3FiniteDirichletInterCellHeightCross_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun M : ℕ => canonicalC3FiniteDirichletInterCellHeightCross M s)
      Filter.atTop
      (nhds
        ((scalarBoundaryWedge
            (bracketedDirichletChart 3 s)
            (Complex.I *
              canonicalCompletedC3EnrichedTfvdLogJetTailReadout s)).im -
          ∑' m : ℕ, canonicalC3DirichletCellHeightTerm m s)) := by
  have hglobal := finiteC3HeightBoundaryWedge_im_tendsto hs
  have hlocal := canonicalC3FiniteDirichletCellLocalHeightReadout_tendsto hs
  have hdifference := hglobal.sub hlocal
  apply hdifference.congr'
  exact Filter.Eventually.of_forall fun M => by
    change
      (scalarBoundaryWedge
          (finiteBracketedDirichletChart 3 M s)
          (Complex.I * finiteCanonicalLogBracketChart M s)).im -
          canonicalC3FiniteDirichletCellLocalHeightReadout M s =
        canonicalC3FiniteDirichletInterCellHeightCross M s
    rw [finiteC3HeightBoundaryWedge_im_eq_cellLocal_add_interCellCross]
    ring

/-! ## Stable completed cell ledger -/

/-- Completed contribution of the stable signed cell-local series. -/
def canonicalC3FiniteCompletedCellLocalHeightReadout
    (M : ℕ) (z : ℂ) : ℝ :=
  Complex.normSq (nativeXiCompletionFactor z) *
    canonicalC3FiniteDirichletCellLocalHeightReadout M
      (operatorHeightParameter z)

/-- Completed nonlocal channel after within-cell compensation has already
been absorbed: inter-cell provenance plus the archimedean/chart channel. -/
def canonicalC3FiniteCompletedInterCellArchReadout
    (M : ℕ) (z : ℂ) : ℝ :=
  Complex.normSq (nativeXiCompletionFactor z) *
      canonicalC3FiniteDirichletInterCellHeightCross M
        (operatorHeightParameter z) +
    (canonicalCompletedC3ArchimedeanChartMixedChannel z z).im

/-- Limit of the completed signed local-cell channel. -/
def canonicalCompletedC3CellLocalHeightReadout (z : ℂ) : ℝ :=
  Complex.normSq (nativeXiCompletionFactor z) *
    ∑' m : ℕ,
      canonicalC3DirichletCellHeightTerm m (operatorHeightParameter z)

/-- Limit of the completed inter-cell and archimedean channels. -/
def canonicalCompletedC3InterCellArchReadout (z : ℂ) : ℝ :=
  Complex.normSq (nativeXiCompletionFactor z) *
      ((scalarBoundaryWedge
          (bracketedDirichletChart 3 (operatorHeightParameter z))
          (Complex.I *
            canonicalCompletedC3EnrichedTfvdLogJetTailReadout
              (operatorHeightParameter z))).im -
        ∑' m : ℕ,
          canonicalC3DirichletCellHeightTerm m (operatorHeightParameter z)) +
    (canonicalCompletedC3ArchimedeanChartMixedChannel z z).im

/-- Exact completed ledger after geometrically stable cell regrouping. -/
theorem canonicalC3FiniteCompletedChiralEnergyLedger_eq_cellLocal_add_interCellArch
    (M : ℕ) (z : ℂ) :
    canonicalC3FiniteCompletedChiralEnergyLedger M z =
      canonicalC3FiniteCompletedCellLocalHeightReadout M z +
        canonicalC3FiniteCompletedInterCellArchReadout M z := by
  unfold canonicalC3FiniteCompletedChiralEnergyLedger
    canonicalC3FiniteRawHeightBoundaryWedge
    canonicalC3FiniteCompletedCellLocalHeightReadout
    canonicalC3FiniteCompletedInterCellArchReadout
  rw [mixedHermitianWeight_self_eq_normSq,
    Complex.add_im, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [finiteC3HeightBoundaryWedge_im_eq_cellLocal_add_interCellCross]
  ring

/-- The completed cell-local channel converges separately. -/
theorem canonicalC3FiniteCompletedCellLocalHeightReadout_tendsto
    {z : ℂ} (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ => canonicalC3FiniteCompletedCellLocalHeightReadout M z)
      Filter.atTop
      (nhds (canonicalCompletedC3CellLocalHeightReadout z)) := by
  unfold canonicalC3FiniteCompletedCellLocalHeightReadout
    canonicalCompletedC3CellLocalHeightReadout
  exact tendsto_const_nhds.mul
    (canonicalC3FiniteDirichletCellLocalHeightReadout_tendsto hz.1)

/-- The completed inter-cell-plus-archimedean channel converges separately. -/
theorem canonicalC3FiniteCompletedInterCellArchReadout_tendsto
    {z : ℂ} (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ => canonicalC3FiniteCompletedInterCellArchReadout M z)
      Filter.atTop
      (nhds (canonicalCompletedC3InterCellArchReadout z)) := by
  unfold canonicalC3FiniteCompletedInterCellArchReadout
    canonicalCompletedC3InterCellArchReadout
  have hcross :=
    canonicalC3FiniteDirichletInterCellHeightCross_tendsto hz.1
  exact (tendsto_const_nhds.mul hcross).add tendsto_const_nhds

/-- Stable center--leg completion square: the two separately convergent cell
channels sum exactly to the completed full chiral balance. -/
theorem canonicalCompletedC3CellLedger_eq_fullChiralBalance
    (carrierCutoff : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    canonicalCompletedC3CellLocalHeightReadout z +
        canonicalCompletedC3InterCellArchReadout z =
      (mixedHermitianWeight canonicalC3ChartFactorHeight z z *
          canonicalCompletedC3GammaCharacteristicWeight z z *
          (Complex.I *
            (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
                carrierCutoff z z -
              canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
                carrierCutoff z z))).im := by
  have hcells :=
    (canonicalC3FiniteCompletedCellLocalHeightReadout_tendsto hz).add
      (canonicalC3FiniteCompletedInterCellArchReadout_tendsto hz)
  have hledger :
      Filter.Tendsto
        (fun M : ℕ => canonicalC3FiniteCompletedChiralEnergyLedger M z)
        Filter.atTop
        (nhds
          (canonicalCompletedC3CellLocalHeightReadout z +
            canonicalCompletedC3InterCellArchReadout z)) := by
    apply hcells.congr'
    exact Filter.Eventually.of_forall fun M =>
      (canonicalC3FiniteCompletedChiralEnergyLedger_eq_cellLocal_add_interCellArch
        M z).symm
  exact tendsto_nhds_unique hledger
    (canonicalC3FiniteCompletedChiralEnergyLedger_tendsto_fullChiralBalance
      carrierCutoff hz hF)

/-- The final completed sign gate in terms of two finite, separately
convergent geometric channels. -/
theorem canonicalCompletedC3FullChiralBalance_im_nonneg_iff_interCellArch_le_cellLocal
    (carrierCutoff : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    0 ≤
        (mixedHermitianWeight canonicalC3ChartFactorHeight z z *
          canonicalCompletedC3GammaCharacteristicWeight z z *
          (Complex.I *
            (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
                carrierCutoff z z -
              canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
                carrierCutoff z z))).im ↔
      -canonicalCompletedC3InterCellArchReadout z ≤
        canonicalCompletedC3CellLocalHeightReadout z := by
  rw [← canonicalCompletedC3CellLedger_eq_fullChiralBalance
    carrierCutoff hz hF]
  constructor <;> intro h <;> linarith

/-- On the diagonal, the characteristic normalization is twice the squared
modulus of the completed characteristic. -/
theorem canonicalCompletedC3GammaCharacteristicWeight_self_eq_normSq
    (z : ℂ) :
    canonicalCompletedC3GammaCharacteristicWeight z z =
      ((2 * Complex.normSq (completedNativeOperatorCharacteristic z) : ℝ) :
        ℂ) := by
  unfold canonicalCompletedC3GammaCharacteristicWeight
  calc
    (2 : ℂ) * conj (completedNativeOperatorCharacteristic z) *
          completedNativeOperatorCharacteristic z =
        (2 : ℂ) * (completedNativeOperatorCharacteristic z *
          conj (completedNativeOperatorCharacteristic z)) := by ring
    _ = ((2 * Complex.normSq
          (completedNativeOperatorCharacteristic z) : ℝ) : ℂ) := by
      rw [Complex.mul_conj]
      norm_cast

/-- Exact diagonal scale of the completed cell ledger.  The spectral
separation contributes the factor 2 times the height imaginary part; both
completion weights become squared moduli. -/
theorem canonicalCompletedC3FullChiralBalance_im_eq_weighted_dslope
    (carrierCutoff : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : z.im ≠ 0) :
    (mixedHermitianWeight canonicalC3ChartFactorHeight z z *
          canonicalCompletedC3GammaCharacteristicWeight z z *
          (Complex.I *
            (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
                carrierCutoff z z -
              canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
                carrierCutoff z z))).im =
      4 * Complex.normSq (canonicalC3ChartFactorHeight z) *
        Complex.normSq (completedNativeOperatorCharacteristic z) * z.im *
        (canonicalCompletedNativePolarizedDslopeKernel z z).re := by
  have hsep : z ≠ conj z := by
    intro heq
    have him := congrArg Complex.im heq
    rw [Complex.conj_im] at him
    exact hzIm (by linarith)
  rw [
    canonicalCompletedC3FullWronskianChiralDifference_eq_separation_mul_dslope
      carrierCutoff hz hz hF hF hsep,
    mixedHermitianWeight_self_eq_normSq,
    canonicalCompletedC3GammaCharacteristicWeight_self_eq_normSq]
  simp [Complex.mul_im, Complex.mul_re]
  ring

/-- In the upper height half-plane, the stable geometric cell inequality is
equivalent to diagonal completed-native dslope positivity. -/
theorem
    canonicalCompletedC3InterCellArch_le_cellLocal_iff_dslope_re_nonneg
    (carrierCutoff : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    -canonicalCompletedC3InterCellArchReadout z ≤
        canonicalCompletedC3CellLocalHeightReadout z ↔
      0 ≤ (canonicalCompletedNativePolarizedDslopeKernel z z).re := by
  rw [←
    canonicalCompletedC3FullChiralBalance_im_nonneg_iff_interCellArch_le_cellLocal
      carrierCutoff hz hF,
    canonicalCompletedC3FullChiralBalance_im_eq_weighted_dslope
      carrierCutoff hz hF (ne_of_gt hzIm)]
  have hchart :
      0 < Complex.normSq (canonicalC3ChartFactorHeight z) :=
    Complex.normSq_pos.mpr (canonicalC3ChartFactorHeight_ne_zero hz)
  have hcharacteristic :
      0 < Complex.normSq (completedNativeOperatorCharacteristic z) :=
    Complex.normSq_pos.mpr hF
  have hscale :
      0 <
        4 * Complex.normSq (canonicalC3ChartFactorHeight z) *
          Complex.normSq (completedNativeOperatorCharacteristic z) * z.im := by
    positivity
  constructor <;> intro h <;> nlinarith

end

end CarrySelfAdjointOperator

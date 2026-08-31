import CarrySelfAdjointOperator.CompletedNativeCausalLegChiralBridge
import Mathlib.Tactic

/-!
# Native Dirichlet chiral cross ledger

A single native Dirichlet atom and its logarithmic jet have zero scalar
boundary wedge: multiplication by the real frequency `log n` cannot create a
signed chiral imbalance.  Consequently, for every finite family of native
atoms, the complete chiral boundary is carried entirely by ordered
cross-frequency provenance.

This is an exact finite identity.  It introduces no positivity, zero-set, or
spectral hypothesis and does not discard any ordered pair.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- One native Dirichlet atom has no signed chiral imbalance by itself. -/
@[simp] theorem scalarBoundaryWedge_natDirichletTerm_eq_zero
    (s : ℂ) (n : ℕ) :
    scalarBoundaryWedge
        (natDirichletTerm s n)
        (natLogDirichletTerm s n) = 0 := by
  unfold scalarBoundaryWedge natLogDirichletTerm
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- Every ordered pair is the frequency difference times the Hermitian
product of its two native atoms. -/
theorem scalarBoundaryPairCell_natDirichletTerm
    (s : ℂ) (i j : ℕ) :
    scalarBoundaryPairCell
        (fun n : ℕ => natDirichletTerm s n)
        (fun n : ℕ => natLogDirichletTerm s n) i j =
      (((Real.log (j : ℝ) - Real.log (i : ℝ) : ℝ) : ℂ) *
        (starRingEnd ℂ) (natDirichletTerm s i) *
        natDirichletTerm s j) := by
  unfold scalarBoundaryPairCell natLogDirichletTerm
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- In a finite native family all diagonal wedges vanish, so the synthesized
boundary is exactly its cross-frequency provenance. -/
theorem scalarBoundaryWedge_sum_natDirichletTerm_eq_crossProvenance
    {ι : Type*} [Fintype ι]
    (index : ι → ℕ) (s : ℂ) :
    scalarBoundaryWedge
        (∑ i : ι, natDirichletTerm s (index i))
        (∑ i : ι, natLogDirichletTerm s (index i)) =
      scalarBoundaryCrossProvenance
        (fun i : ι => natDirichletTerm s (index i))
        (fun i : ι => natLogDirichletTerm s (index i)) := by
  rw [scalarBoundaryWedge_sum_eq_local_add_crossProvenance]
  simp

/-- Fully expanded ordered-pair formula for the native cross provenance. -/
theorem scalarBoundaryCrossProvenance_natDirichletTerm_eq_pairwise
    {ι : Type*} [Fintype ι]
    (index : ι → ℕ) (s : ℂ) :
    scalarBoundaryCrossProvenance
        (fun i : ι => natDirichletTerm s (index i))
        (fun i : ι => natLogDirichletTerm s (index i)) =
      ∑ i : ι, ∑ j : ι,
        (((Real.log (index j : ℝ) - Real.log (index i : ℝ) : ℝ) : ℂ) *
          (starRingEnd ℂ) (natDirichletTerm s (index i)) *
          natDirichletTerm s (index j)) := by
  unfold scalarBoundaryCrossProvenance scalarBoundaryPairwiseLedger
  simp only [scalarBoundaryWedge_natDirichletTerm_eq_zero,
    Finset.sum_const_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact scalarBoundaryPairCell_natDirichletTerm s (index i) (index j)

/-- The global scalar chiral difference of a finite native family is therefore
exactly `i` times its explicit cross-frequency ledger. -/
theorem scalarChiralDifference_sum_natDirichletTerm_eq_crossProvenance
    {ι : Type*} [Fintype ι]
    (index : ι → ℕ) (s : ℂ) :
    Complex.I *
        (inner ℂ
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2
                (∑ i : ι, natLogDirichletTerm s (index i),
                  ∑ i : ι, natDirichletTerm s (index i))))
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2
                (∑ i : ι, natLogDirichletTerm s (index i),
                  ∑ i : ι, natDirichletTerm s (index i)))) -
          inner ℂ
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2
                (∑ i : ι, natLogDirichletTerm s (index i),
                  ∑ i : ι, natDirichletTerm s (index i))))
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2
                (∑ i : ι, natLogDirichletTerm s (index i),
                  ∑ i : ι, natDirichletTerm s (index i))))) =
      scalarBoundaryCrossProvenance
        (fun i : ι => natDirichletTerm s (index i))
        (fun i : ι => natLogDirichletTerm s (index i)) := by
  rw [← scalarBoundaryWedge_eq_scalarChiralDifference]
  exact scalarBoundaryWedge_sum_natDirichletTerm_eq_crossProvenance index s

/-! ## Real-weighted native atoms -/

/-- A real coefficient preserves the zero local wedge of a native atom. -/
@[simp] theorem scalarBoundaryWedge_realWeightedNatDirichletTerm_eq_zero
    (weight : ℝ) (s : ℂ) (n : ℕ) :
    scalarBoundaryWedge
        ((weight : ℂ) * natDirichletTerm s n)
        ((weight : ℂ) * natLogDirichletTerm s n) = 0 := by
  unfold scalarBoundaryWedge natLogDirichletTerm
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- Exact ordered-pair formula after retaining arbitrary real synthesis
weights. -/
theorem scalarBoundaryPairCell_realWeightedNatDirichletTerm
    {ι : Type*} (weight : ι → ℝ) (index : ι → ℕ)
    (s : ℂ) (i j : ι) :
    scalarBoundaryPairCell
        (fun k : ι => (weight k : ℂ) * natDirichletTerm s (index k))
        (fun k : ι => (weight k : ℂ) * natLogDirichletTerm s (index k))
        i j =
      (((weight i * weight j *
          (Real.log (index j : ℝ) - Real.log (index i : ℝ)) : ℝ) : ℂ) *
        (starRingEnd ℂ) (natDirichletTerm s (index i)) *
        natDirichletTerm s (index j)) := by
  unfold scalarBoundaryPairCell natLogDirichletTerm
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-! ## The exact finite C3 coefficient family -/

/-- Provenance type of the finite C3 chart: one seed and three atoms for each
complete bracket cell. -/
abbrev CanonicalC3FiniteDirichletAtom (M : ℕ) :=
  Unit ⊕ (Fin M × Fin 3)

/-- Natural Dirichlet index carried by one provenance-labelled C3 atom. -/
def canonicalC3FiniteDirichletAtomIndex
    {M : ℕ} : CanonicalC3FiniteDirichletAtom M → ℕ
  | Sum.inl _ => 1
  | Sum.inr atom => 3 * (atom.1 : ℕ) + (atom.2 : ℕ) + 2

/-- Exact real coefficient of one C3 atom.  The center is `-2`; both legs and
the seed have coefficient `1`. -/
def canonicalC3FiniteDirichletAtomWeight
    {M : ℕ} : CanonicalC3FiniteDirichletAtom M → ℝ
  | Sum.inl _ => 1
  | Sum.inr atom => if (atom.2 : ℕ) = 1 then -2 else 1

/-- Value channel of one provenance-labelled finite C3 atom. -/
def canonicalC3FiniteDirichletValueAtom
    (M : ℕ) (s : ℂ) (atom : CanonicalC3FiniteDirichletAtom M) : ℂ :=
  (canonicalC3FiniteDirichletAtomWeight atom : ℂ) *
    natDirichletTerm s (canonicalC3FiniteDirichletAtomIndex atom)

/-- Log-jet channel of the same finite C3 atom. -/
def canonicalC3FiniteDirichletLogJetAtom
    (M : ℕ) (s : ℂ) (atom : CanonicalC3FiniteDirichletAtom M) : ℂ :=
  (canonicalC3FiniteDirichletAtomWeight atom : ℂ) *
    natLogDirichletTerm s (canonicalC3FiniteDirichletAtomIndex atom)

/-- The three labelled atoms in one C3 cell sum to its genuine bracket. -/
theorem canonicalC3FiniteDirichletValueAtom_cellSum
    {M : ℕ} (m : Fin M) (s : ℂ) :
    ∑ r : Fin 3,
        canonicalC3FiniteDirichletValueAtom M s (Sum.inr (m, r)) =
      realCpSaturatedBracket 3 m s := by
  rw [realCpSaturatedBracket_three_eq_values]
  simp [canonicalC3FiniteDirichletValueAtom,
    canonicalC3FiniteDirichletAtomWeight,
    canonicalC3FiniteDirichletAtomIndex, Fin.sum_univ_succ]
  ring

/-- The three labelled log atoms in one C3 cell sum to its canonical
log-bracket block. -/
theorem canonicalC3FiniteDirichletLogJetAtom_cellSum
    {M : ℕ} (m : Fin M) (s : ℂ) :
    ∑ r : Fin 3,
        canonicalC3FiniteDirichletLogJetAtom M s (Sum.inr (m, r)) =
      canonicalLogBracketBlock m s := by
  simp [canonicalC3FiniteDirichletLogJetAtom,
    canonicalC3FiniteDirichletAtomWeight,
    canonicalC3FiniteDirichletAtomIndex,
    canonicalLogBracketBlock,
    positiveLogDirichletValue_eq_natLogDirichletTerm,
    Fin.sum_univ_succ]
  ring

/-- The complete provenance-labelled value family is literally the existing
finite bracketed C3 chart, including its seed. -/
theorem canonicalC3FiniteDirichletValueAtom_sum_eq_valueChart
    (M : ℕ) (s : ℂ) :
    ∑ atom : CanonicalC3FiniteDirichletAtom M,
        canonicalC3FiniteDirichletValueAtom M s atom =
      finiteBracketedDirichletChart 3 M s := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [canonicalC3FiniteDirichletValueAtom_cellSum]
  unfold finiteBracketedDirichletChart
  rw [seedSum_three_dirichlet_eq_one]
  simp [canonicalC3FiniteDirichletValueAtom,
    canonicalC3FiniteDirichletAtomWeight,
    canonicalC3FiniteDirichletAtomIndex, natDirichletTerm, dirichletTerm]
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => realCpSaturatedBracket 3 k s) M

/-- The complete provenance-labelled log family is literally the existing
finite canonical log-jet chart; the seed contributes `log 1 = 0`. -/
theorem canonicalC3FiniteDirichletLogJetAtom_sum_eq_logJetChart
    (M : ℕ) (s : ℂ) :
    ∑ atom : CanonicalC3FiniteDirichletAtom M,
        canonicalC3FiniteDirichletLogJetAtom M s atom =
      finiteCanonicalLogBracketChart M s := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [canonicalC3FiniteDirichletLogJetAtom_cellSum]
  unfold finiteCanonicalLogBracketChart
  simp [canonicalC3FiniteDirichletLogJetAtom,
    canonicalC3FiniteDirichletAtomWeight,
    canonicalC3FiniteDirichletAtomIndex, natLogDirichletTerm]
  exact Fin.sum_univ_eq_sum_range
    (fun m : ℕ => canonicalLogBracketBlock m s) M

/-- Every provenance-labelled atom in the finite C3 chart has zero local
chiral wedge. -/
@[simp] theorem canonicalC3FiniteDirichletAtom_localWedge_eq_zero
    (M : ℕ) (s : ℂ) (atom : CanonicalC3FiniteDirichletAtom M) :
    scalarBoundaryWedge
        (canonicalC3FiniteDirichletValueAtom M s atom)
        (canonicalC3FiniteDirichletLogJetAtom M s atom) = 0 := by
  exact scalarBoundaryWedge_realWeightedNatDirichletTerm_eq_zero
    (canonicalC3FiniteDirichletAtomWeight atom) s
    (canonicalC3FiniteDirichletAtomIndex atom)

/-- Exact finite C3 route-B identity: the complete value/log-jet boundary
readout is carried entirely by the off-diagonal provenance ledger. -/
theorem finiteBracketedDirichletChart_scalarBoundaryWedge_eq_crossProvenance
    (M : ℕ) (s : ℂ) :
    scalarBoundaryWedge
        (finiteBracketedDirichletChart 3 M s)
        (finiteCanonicalLogBracketChart M s) =
      scalarBoundaryCrossProvenance
        (canonicalC3FiniteDirichletValueAtom M s)
        (canonicalC3FiniteDirichletLogJetAtom M s) := by
  rw [← canonicalC3FiniteDirichletValueAtom_sum_eq_valueChart,
    ← canonicalC3FiniteDirichletLogJetAtom_sum_eq_logJetChart,
    scalarBoundaryWedge_sum_eq_local_add_crossProvenance]
  simp

/-! ## Height rotation: positive local energy plus crossed provenance -/

/-- The height-coordinate companion of one C3 atom.  The quarter turn is
forced by `s = 1 / 2 + i z`. -/
def canonicalC3FiniteDirichletHeightCompanionAtom
    (M : ℕ) (s : ℂ) (atom : CanonicalC3FiniteDirichletAtom M) : ℂ :=
  Complex.I * canonicalC3FiniteDirichletLogJetAtom M s atom

/-- Every labelled C3 atom has a positive natural index. -/
theorem canonicalC3FiniteDirichletAtomIndex_pos
    {M : ℕ} (atom : CanonicalC3FiniteDirichletAtom M) :
    0 < canonicalC3FiniteDirichletAtomIndex atom := by
  rcases atom with seed | atom
  · simp [canonicalC3FiniteDirichletAtomIndex]
  · simp [canonicalC3FiniteDirichletAtomIndex]

/-- Exact local height energy of one native atom. -/
theorem canonicalC3FiniteDirichletAtom_heightWedge_im
    (M : ℕ) (s : ℂ) (atom : CanonicalC3FiniteDirichletAtom M) :
    (scalarBoundaryWedge
        (canonicalC3FiniteDirichletValueAtom M s atom)
        (canonicalC3FiniteDirichletHeightCompanionAtom M s atom)).im =
      2 * (canonicalC3FiniteDirichletAtomWeight atom) ^ 2 *
        Real.log (canonicalC3FiniteDirichletAtomIndex atom : ℝ) *
        Complex.normSq
          (natDirichletTerm s
            (canonicalC3FiniteDirichletAtomIndex atom)) := by
  rw [canonicalC3FiniteDirichletHeightCompanionAtom,
    scalarBoundaryWedge_value_I_mul_logJet_im]
  unfold canonicalC3FiniteDirichletValueAtom
    canonicalC3FiniteDirichletLogJetAtom natLogDirichletTerm
  simp only [map_mul, Complex.conj_ofReal]
  simp [Complex.mul_re, Complex.normSq_apply]
  rw [← Complex.natCast_log]
  simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero,
    zero_mul, add_zero]
  ring

/-- The local height energy of every C3 atom is nonnegative. -/
theorem canonicalC3FiniteDirichletAtom_heightWedge_im_nonneg
    (M : ℕ) (s : ℂ) (atom : CanonicalC3FiniteDirichletAtom M) :
    0 ≤
      (scalarBoundaryWedge
        (canonicalC3FiniteDirichletValueAtom M s atom)
        (canonicalC3FiniteDirichletHeightCompanionAtom M s atom)).im := by
  rw [canonicalC3FiniteDirichletAtom_heightWedge_im]
  have hindex : (1 : ℝ) ≤
      (canonicalC3FiniteDirichletAtomIndex atom : ℝ) := by
    exact_mod_cast canonicalC3FiniteDirichletAtomIndex_pos atom
  have hlog : 0 ≤
      Real.log (canonicalC3FiniteDirichletAtomIndex atom : ℝ) :=
    Real.log_nonneg hindex
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _)) hlog)
    (Complex.normSq_nonneg _)

/-- Sum of all local positive height energies at one C3 cutoff. -/
def canonicalC3FiniteDirichletLocalHeightEnergy
    (M : ℕ) (s : ℂ) : ℝ :=
  ∑ atom : CanonicalC3FiniteDirichletAtom M,
    2 * (canonicalC3FiniteDirichletAtomWeight atom) ^ 2 *
      Real.log (canonicalC3FiniteDirichletAtomIndex atom : ℝ) *
      Complex.normSq
        (natDirichletTerm s
          (canonicalC3FiniteDirichletAtomIndex atom))

/-- The complete local height-energy sum is nonnegative at every cutoff. -/
theorem canonicalC3FiniteDirichletLocalHeightEnergy_nonneg
    (M : ℕ) (s : ℂ) :
    0 ≤ canonicalC3FiniteDirichletLocalHeightEnergy M s := by
  unfold canonicalC3FiniteDirichletLocalHeightEnergy
  apply Finset.sum_nonneg
  intro atom hatom
  rw [← canonicalC3FiniteDirichletAtom_heightWedge_im]
  exact canonicalC3FiniteDirichletAtom_heightWedge_im_nonneg M s atom

/-- The atomwise height companions synthesize exactly the quarter-turned
finite canonical log-jet chart. -/
theorem canonicalC3FiniteDirichletHeightCompanionAtom_sum_eq
    (M : ℕ) (s : ℂ) :
    ∑ atom : CanonicalC3FiniteDirichletAtom M,
        canonicalC3FiniteDirichletHeightCompanionAtom M s atom =
      Complex.I * finiteCanonicalLogBracketChart M s := by
  unfold canonicalC3FiniteDirichletHeightCompanionAtom
  rw [← Finset.mul_sum,
    canonicalC3FiniteDirichletLogJetAtom_sum_eq_logJetChart]

/-- Exact finite route-B ledger in the height coordinate: positive local
energy plus the complete ordered cross provenance, with no channel erased. -/
theorem finiteC3HeightBoundaryWedge_im_eq_localEnergy_add_crossProvenance
    (M : ℕ) (s : ℂ) :
    (scalarBoundaryWedge
        (finiteBracketedDirichletChart 3 M s)
        (Complex.I * finiteCanonicalLogBracketChart M s)).im =
      canonicalC3FiniteDirichletLocalHeightEnergy M s +
        (scalarBoundaryCrossProvenance
          (canonicalC3FiniteDirichletValueAtom M s)
          (canonicalC3FiniteDirichletHeightCompanionAtom M s)).im := by
  rw [← canonicalC3FiniteDirichletValueAtom_sum_eq_valueChart,
    ← canonicalC3FiniteDirichletHeightCompanionAtom_sum_eq,
    scalarBoundaryWedge_sum_eq_local_add_crossProvenance]
  have hsumIm :
      (∑ atom : CanonicalC3FiniteDirichletAtom M,
        scalarBoundaryWedge
          (canonicalC3FiniteDirichletValueAtom M s atom)
          (canonicalC3FiniteDirichletHeightCompanionAtom M s atom)).im =
        ∑ atom : CanonicalC3FiniteDirichletAtom M,
          (scalarBoundaryWedge
            (canonicalC3FiniteDirichletValueAtom M s atom)
            (canonicalC3FiniteDirichletHeightCompanionAtom M s atom)).im := by
    exact
      (Complex.im_sum
        (s := Finset.univ)
        (fun atom : CanonicalC3FiniteDirichletAtom M =>
          scalarBoundaryWedge
            (canonicalC3FiniteDirichletValueAtom M s atom)
            (canonicalC3FiniteDirichletHeightCompanionAtom M s atom)))
  rw [Complex.add_im, hsumIm]
  congr 1
  unfold canonicalC3FiniteDirichletLocalHeightEnergy
  apply Finset.sum_congr rfl
  intro atom hatom
  exact canonicalC3FiniteDirichletAtom_heightWedge_im M s atom

/-- The finite height readout is nonnegative exactly when the crossed ledger
cannot outweigh the positive local energy. -/
theorem finiteC3HeightBoundaryWedge_im_nonneg_iff_cross_le_localEnergy
    (M : ℕ) (s : ℂ) :
    0 ≤
        (scalarBoundaryWedge
          (finiteBracketedDirichletChart 3 M s)
          (Complex.I * finiteCanonicalLogBracketChart M s)).im ↔
      -(scalarBoundaryCrossProvenance
          (canonicalC3FiniteDirichletValueAtom M s)
          (canonicalC3FiniteDirichletHeightCompanionAtom M s)).im ≤
        canonicalC3FiniteDirichletLocalHeightEnergy M s := by
  rw [finiteC3HeightBoundaryWedge_im_eq_localEnergy_add_crossProvenance]
  constructor <;> intro h <;> linarith

/-! ## Passage of the complete crossed ledger to the native limit -/

/-- Continuity of the scalar boundary wedge under simultaneous convergence
of its value and companion channels. -/
theorem scalarBoundaryWedge_tendsto
    {α : Type*} {l : Filter α}
    {value logJet : α → ℂ} {valueLimit logJetLimit : ℂ}
    (hvalue : Filter.Tendsto value l (nhds valueLimit))
    (hlogJet : Filter.Tendsto logJet l (nhds logJetLimit)) :
    Filter.Tendsto
      (fun n => scalarBoundaryWedge (value n) (logJet n)) l
      (nhds (scalarBoundaryWedge valueLimit logJetLimit)) := by
  simpa [scalarBoundaryWedge] using
    (hvalue.star.mul hlogJet).sub (hlogJet.star.mul hvalue)

/-- The finite unrotated cross provenance converges to the raw native
value/log-jet boundary wedge.  Both limits come from the existing exact
head--tail completion. -/
theorem canonicalC3FiniteDirichletCrossProvenance_tendsto_rawBoundaryWedge
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun M : ℕ =>
        scalarBoundaryCrossProvenance
          (canonicalC3FiniteDirichletValueAtom M s)
          (canonicalC3FiniteDirichletLogJetAtom M s))
      Filter.atTop
      (nhds
        (scalarBoundaryWedge
          (bracketedDirichletChart 3 s)
          (canonicalCompletedC3EnrichedTfvdLogJetTailReadout s))) := by
  have hvalue := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) (s := s) (by linarith)
  have hlogJet := finiteCanonicalLogBracketChart_tendsto_completed hs
  have hwedge := scalarBoundaryWedge_tendsto hvalue hlogJet
  apply hwedge.congr'
  exact Filter.Eventually.of_forall fun M =>
    finiteBracketedDirichletChart_scalarBoundaryWedge_eq_crossProvenance M s

/-- The complete route-B ledger, local energy plus crossed provenance,
converges without splitting its two channels to the correctly quarter-turned
native height boundary wedge. -/
theorem canonicalC3FiniteHeightEnergyLedger_tendsto_rawHeightBoundaryWedge
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteDirichletLocalHeightEnergy M s +
          (scalarBoundaryCrossProvenance
            (canonicalC3FiniteDirichletValueAtom M s)
            (canonicalC3FiniteDirichletHeightCompanionAtom M s)).im)
      Filter.atTop
      (nhds
        (scalarBoundaryWedge
          (bracketedDirichletChart 3 s)
          (Complex.I *
            canonicalCompletedC3EnrichedTfvdLogJetTailReadout s)).im) := by
  have hvalue := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) (s := s) (by linarith)
  have hlogJet := finiteCanonicalLogBracketChart_tendsto_completed hs
  have hheightLogJet := hlogJet.const_mul Complex.I
  have hwedge := scalarBoundaryWedge_tendsto hvalue hheightLogJet
  have him := Complex.continuous_im.continuousAt.tendsto.comp hwedge
  apply him.congr'
  exact Filter.Eventually.of_forall fun M => by
    simpa [Function.comp_apply] using
      finiteC3HeightBoundaryWedge_im_eq_localEnergy_add_crossProvenance M s

/-- On the diagonal, the raw completed C3 Wronskian is the same scalar
boundary wedge used by the finite crossed ledger. -/
theorem canonicalCompletedC3RawHeightMixedWronskian_self_eq_scalarBoundaryWedge
    (z : ℂ) :
    canonicalCompletedC3RawHeightMixedWronskian z z =
      scalarBoundaryWedge
        (canonicalCompletedC3RawHeightValue z)
        (canonicalCompletedC3RawHeightCompanion z) := by
  unfold canonicalCompletedC3RawHeightMixedWronskian
    completedGreenWronskian scalarBoundaryWedge
  ring

/-- Height-coordinate specialization: the complete finite route-B ledger
converges exactly to the diagonal raw C3 Wronskian. -/
theorem canonicalC3FiniteHeightEnergyLedger_tendsto_rawHeightWronskian
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteDirichletLocalHeightEnergy M
            (operatorHeightParameter z) +
          (scalarBoundaryCrossProvenance
            (canonicalC3FiniteDirichletValueAtom M
              (operatorHeightParameter z))
            (canonicalC3FiniteDirichletHeightCompanionAtom M
              (operatorHeightParameter z))).im)
      Filter.atTop
      (nhds (canonicalCompletedC3RawHeightMixedWronskian z z).im) := by
  have hlimit :=
    canonicalC3FiniteHeightEnergyLedger_tendsto_rawHeightBoundaryWedge hz.1
  rw [canonicalCompletedC3RawHeightMixedWronskian_self_eq_scalarBoundaryWedge]
  rw [canonicalCompletedC3RawHeightValue_eq_bracketedDirichletChart hz]
  exact hlimit

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedC3FourCornerGreenCell
import CarrySelfAdjointOperator.CompletedNativeTfvdEnrichedTaylorMomentIdentification
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# All-order Taylor Gram of the native four-corner cell

The complete native `G_pre` cell already realizes the product of two
consecutive slopes.  This module applies that identity before scalar
completion to the exact logarithmic-orbit Taylor atoms.  It proves that the
resulting finite cell sums are precisely the Gram entries of the finite TFVD
Taylor prefixes and that they converge to the completed `ell^2` Taylor Gram.

The parity Gram towers of the enriched ordinary/log-jet carrier are then
strictly positive by the all-order Vandermonde independence already proved
for the same vectors.  No completed moment identification, characteristic
zero, spectral premise, or positivity assumption is used.
-/

open scoped Topology BigOperators lp ENNReal NNReal InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-! ## Taylor atoms inside one complete four-corner cell -/

/-- Taylor atom of one centered native Dirichlet coordinate. -/
def nativeDirichletTaylorAtom (order m : ℕ) : ℂ :=
  nativeCriticalDirichletAmplitude m *
    (-Complex.I * (Real.log (m : ℝ) : ℂ)) ^ order /
      (order.factorial : ℂ)

/-- The completed slope coefficient is the consecutive difference of the
same Taylor atoms that enter the four-corner product. -/
theorem nativeDirichletSlopeTaylorCoefficient_eq_atom_sub
    (order n : ℕ) :
    nativeDirichletSlopeTaylorCoefficient order n =
      nativeDirichletTaylorAtom order (n + 2) -
        nativeDirichletTaylorAtom order (n + 1) := by
  rfl

/-- Four-corner product target specialized to two independent Taylor orders. -/
def nativeGpreFourCornerTaylorProductTarget
    (edge p q : ℕ) (corner : GpreCorner) : ℂ :=
  nativeGpreFourCornerProductTarget edge
    (nativeDirichletTaylorAtom p)
    (nativeDirichletTaylorAtom q) corner

/-- One complete Taylor cell, with all four provenance labels retained until
the native scalar readout. -/
def nativeGpreFourCornerTaylorCell (n p q : ℕ) : ℂ :=
  nativeGpreFourCornerComplexReadout (n + 1)
    (nativeGpreFourCornerTaylorProductTarget (n + 1) p q)

/-- Every all-order four-corner Taylor cell is exactly one coefficient Gram
entry. -/
theorem nativeGpreFourCornerTaylorCell_eq_coefficientGram
    (n p q : ℕ) :
    nativeGpreFourCornerTaylorCell n p q =
      (starRingEnd ℂ) (nativeDirichletSlopeTaylorCoefficient p n) *
        nativeDirichletSlopeTaylorCoefficient q n := by
  unfold nativeGpreFourCornerTaylorCell
    nativeGpreFourCornerTaylorProductTarget
  rw [nativeGpreFourCornerComplexReadout_productTarget]
  rfl

/-! ## Finite synthesis and completion -/

/-- Finite synthesis of the all-order four-corner Taylor cells. -/
def nativeGpreFourCornerTaylorPrefix (M p q : ℕ) : ℂ :=
  ∑ n ∈ Finset.range M, nativeGpreFourCornerTaylorCell n p q

/-- A finite four-corner Taylor synthesis is literally the inner product of
the two exact TFVD coefficient prefixes. -/
theorem nativeGpreFourCornerTaylorPrefix_eq_inner
    (M p q : ℕ) :
    nativeGpreFourCornerTaylorPrefix M p q =
      inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState p M)
        (canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState q M) := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := Finset.range M)]
  · unfold nativeGpreFourCornerTaylorPrefix
    apply Finset.sum_congr rfl
    intro n hn
    have hnlt : n < M := Finset.mem_range.mp hn
    rw [nativeGpreFourCornerTaylorCell_eq_coefficientGram]
    simp only [canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState]
    rw [finiteSlopeCoefficientState_apply_of_lt _ hnlt,
      finiteSlopeCoefficientState_apply_of_lt _ hnlt]
    simp [RCLike.inner_apply, mul_comm]
  · intro n hn
    have hnle : M ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    simp only [canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState]
    rw [finiteSlopeCoefficientState_apply_of_le _ hnle,
      finiteSlopeCoefficientState_apply_of_le _ hnle]
    simp

/-- The same finite cell sums converge to the completed all-order Taylor
Gram in the common vertical `ell^2` carrier. -/
theorem nativeGpreFourCornerTaylorPrefix_tendsto_completed
    (p q : ℕ) :
    Tendsto
      (fun M : ℕ => nativeGpreFourCornerTaylorPrefix M p q)
      atTop
      (nhds (inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState p)
        (canonicalCompletedNativeTfvdTaylorCoefficientState q))) := by
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ)
    (canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState_tendsto p)
    (canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState_tendsto q)
  exact hinner.congr' (Eventually.of_forall fun M =>
    (nativeGpreFourCornerTaylorPrefix_eq_inner M p q).symm)

/-! ## Enriched ordinary/log-jet synthesis -/

/-- The completed log-jet Gram is the next ordinary Taylor Gram with the
exact two order weights forced by differentiation. -/
theorem inner_canonicalCompletedNativeTfvdLogTaylorCoefficientState_eq_succ
    (p q : ℕ) :
    inner ℂ
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState p)
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState q) =
      ((p + 1 : ℕ) : ℂ) * ((q + 1 : ℕ) : ℂ) *
        inner ℂ
          (canonicalCompletedNativeTfvdTaylorCoefficientState (p + 1))
          (canonicalCompletedNativeTfvdTaylorCoefficientState (q + 1)) := by
  unfold canonicalCompletedNativeTfvdLogTaylorCoefficientState
  rw [inner_smul_left, inner_smul_right]
  simp only [map_mul, map_natCast, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Channel-complete four-corner synthesis: the ordinary cell and the
shifted cell dictated by the log-jet are kept as separate summands. -/
def nativeGpreFourCornerEnrichedTaylorPrefix (M p q : ℕ) : ℂ :=
  nativeGpreFourCornerTaylorPrefix M p q +
    ((p + 1 : ℕ) : ℂ) * ((q + 1 : ℕ) : ℂ) *
      nativeGpreFourCornerTaylorPrefix M (p + 1) (q + 1)

/-- The completed enriched TFVD Gram is exactly the sum of the two completed
four-corner Taylor channels. -/
theorem inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_eq_fourCorner
    (p q : ℕ) :
    inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet p)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet q) =
      inner ℂ
          (canonicalCompletedNativeTfvdTaylorCoefficientState p)
          (canonicalCompletedNativeTfvdTaylorCoefficientState q) +
        ((p + 1 : ℕ) : ℂ) * ((q + 1 : ℕ) : ℂ) *
          inner ℂ
            (canonicalCompletedNativeTfvdTaylorCoefficientState (p + 1))
            (canonicalCompletedNativeTfvdTaylorCoefficientState (q + 1)) := by
  rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet,
    inner_canonicalCompletedNativeTfvdLogTaylorCoefficientState_eq_succ]

/-- The channel-complete native four-corner prefixes converge to the exact
enriched ordinary/log-jet Gram at every pair of Taylor orders. -/
theorem nativeGpreFourCornerEnrichedTaylorPrefix_tendsto_completed
    (p q : ℕ) :
    Tendsto
      (fun M : ℕ => nativeGpreFourCornerEnrichedTaylorPrefix M p q)
      atTop
      (nhds (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet p)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet q))) := by
  have hord := nativeGpreFourCornerTaylorPrefix_tendsto_completed p q
  have hlog :=
    (nativeGpreFourCornerTaylorPrefix_tendsto_completed (p + 1) (q + 1)).const_mul
      (((p + 1 : ℕ) : ℂ) * ((q + 1 : ℕ) : ℂ))
  have hsum := hord.add hlog
  rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_eq_fourCorner]
  simpa [nativeGpreFourCornerEnrichedTaylorPrefix, mul_assoc] using hsum

/-! ## Strict parity Gram towers before the completed moment readout -/

/-- Real even-parity Gram tower of the channel-complete TFVD Taylor carrier. -/
def canonicalCompletedNativeTfvdEnrichedTaylorEvenGram
    (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (inner ℂ
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * (i : ℕ)))
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * (j : ℕ)))).re

/-- Real odd-parity Gram tower of the channel-complete TFVD Taylor carrier. -/
def canonicalCompletedNativeTfvdEnrichedTaylorOddGram
    (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (inner ℂ
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * (i : ℕ) + 1))
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet
        (2 * (j : ℕ) + 1))).re

/-- Every entry of the even Gram tower is the real limit of the corresponding
channel-complete native four-corner prefixes. -/
theorem nativeGpreFourCornerEnrichedTaylorPrefix_re_tendsto_evenGram
    {N : ℕ} (i j : Fin N) :
    Tendsto
      (fun M : ℕ =>
        (nativeGpreFourCornerEnrichedTaylorPrefix M
          (2 * (i : ℕ)) (2 * (j : ℕ))).re)
      atTop
      (nhds (canonicalCompletedNativeTfvdEnrichedTaylorEvenGram N i j)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (nativeGpreFourCornerEnrichedTaylorPrefix_tendsto_completed
      (2 * (i : ℕ)) (2 * (j : ℕ)))
  change Tendsto
    (fun M : ℕ =>
      (nativeGpreFourCornerEnrichedTaylorPrefix M
        (2 * (i : ℕ)) (2 * (j : ℕ))).re)
    atTop
    (nhds ((inner ℂ
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * (i : ℕ)))
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet
        (2 * (j : ℕ)))).re)) at h
  simpa [Function.comp_apply,
    canonicalCompletedNativeTfvdEnrichedTaylorEvenGram] using h

/-- Every entry of the odd Gram tower is obtained by the identical geometric
limit, with no parity-dependent carrier change. -/
theorem nativeGpreFourCornerEnrichedTaylorPrefix_re_tendsto_oddGram
    {N : ℕ} (i j : Fin N) :
    Tendsto
      (fun M : ℕ =>
        (nativeGpreFourCornerEnrichedTaylorPrefix M
          (2 * (i : ℕ) + 1) (2 * (j : ℕ) + 1)).re)
      atTop
      (nhds (canonicalCompletedNativeTfvdEnrichedTaylorOddGram N i j)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (nativeGpreFourCornerEnrichedTaylorPrefix_tendsto_completed
      (2 * (i : ℕ) + 1) (2 * (j : ℕ) + 1))
  change Tendsto
    (fun M : ℕ =>
      (nativeGpreFourCornerEnrichedTaylorPrefix M
        (2 * (i : ℕ) + 1) (2 * (j : ℕ) + 1)).re)
    atTop
    (nhds ((inner ℂ
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet
        (2 * (i : ℕ) + 1))
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet
        (2 * (j : ℕ) + 1))).re)) at h
  simpa [Function.comp_apply,
    canonicalCompletedNativeTfvdEnrichedTaylorOddGram] using h

/-- The even raw four-corner/log-jet Gram is positive definite at every
finite order.  Strictness comes from the exact all-order coefficient
readout, not from convergence of finite independent families. -/
theorem canonicalCompletedNativeTfvdEnrichedTaylorEvenGram_posDef
    (N : ℕ) :
    (canonicalCompletedNativeTfvdEnrichedTaylorEvenGram N).PosDef := by
  letI : InnerProductSpace ℝ
      CanonicalCompletedNativeTfvdEnrichedTaylorCarrier :=
    InnerProductSpace.rclikeToReal ℂ
      CanonicalCompletedNativeTfvdEnrichedTaylorCarrier
  unfold canonicalCompletedNativeTfvdEnrichedTaylorEvenGram
  change (Matrix.gram ℝ (fun i : Fin N =>
    canonicalCompletedNativeTfvdEnrichedTaylorRawJet (2 * (i : ℕ)))).PosDef
  exact Matrix.posDef_gram_of_linearIndependent
    (canonicalCompletedNativeTfvdEnrichedTaylorEven_linearIndependent
      |>.restrict_scalars' ℝ
      |>.comp (fun i : Fin N => (i : ℕ)) Fin.val_injective)

/-- The odd raw four-corner/log-jet Gram is positive definite at every
finite order by the same exact all-order readout. -/
theorem canonicalCompletedNativeTfvdEnrichedTaylorOddGram_posDef
    (N : ℕ) :
    (canonicalCompletedNativeTfvdEnrichedTaylorOddGram N).PosDef := by
  letI : InnerProductSpace ℝ
      CanonicalCompletedNativeTfvdEnrichedTaylorCarrier :=
    InnerProductSpace.rclikeToReal ℂ
      CanonicalCompletedNativeTfvdEnrichedTaylorCarrier
  unfold canonicalCompletedNativeTfvdEnrichedTaylorOddGram
  change (Matrix.gram ℝ (fun i : Fin N =>
    canonicalCompletedNativeTfvdEnrichedTaylorRawJet
      (2 * (i : ℕ) + 1))).PosDef
  exact Matrix.posDef_gram_of_linearIndependent
    (canonicalCompletedNativeTfvdEnrichedTaylorOdd_linearIndependent
      |>.restrict_scalars' ℝ
      |>.comp (fun i : Fin N => (i : ℕ)) Fin.val_injective)

end

end CarrySelfAdjointOperator

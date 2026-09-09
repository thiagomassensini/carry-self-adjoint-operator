import CarryGeometry.PositionalFoundation

namespace CarrySelfAdjointOperator

open CarryGeometry

/-! The same natural number has compatible quotient-residue coordinates at
successive positional depths. -/

def refinedResidue (b k n : ℕ) : ℕ :=
  residueAtDepth b k n + placeValue b k * (quotientAtDepth b k n % b)

def refinedQuotient (b k n : ℕ) : ℕ :=
  quotientAtDepth b k n / b

/-- The quotient-residue coordinate chart at one positional depth. -/
def positionalDepthCoordinates (b k n : ℕ) : ℕ × ℕ :=
  (quotientAtDepth b k n, residueAtDepth b k n)

/-- The coordinate transport induced by refining one positional window. -/
def positionalDepthRefinement (b k n : ℕ) : ℕ × ℕ :=
  (refinedQuotient b k n, refinedResidue b k n)

theorem residueAtDepth_succ_eq_refinedResidue
    (b k n : ℕ) :
    residueAtDepth b (k + 1) n = refinedResidue b k n := by
  simpa only [residueAtDepth, quotientAtDepth, placeValue, refinedResidue] using
    (Nat.mod_pow_succ (x := n) (b := b) (k := k))

theorem quotientAtDepth_succ_eq_refinedQuotient
    (b k n : ℕ) :
    quotientAtDepth b (k + 1) n = refinedQuotient b k n := by
  unfold quotientAtDepth refinedQuotient placeValue
  exact (Nat.div_div_eq_div_mul n (b ^ k) b).symm

theorem positionalDepthCoordinates_succ_eq_refinement
    (b k n : ℕ) :
    positionalDepthCoordinates b (k + 1) n =
      positionalDepthRefinement b k n := by
  apply Prod.ext
  · exact quotientAtDepth_succ_eq_refinedQuotient b k n
  · exact residueAtDepth_succ_eq_refinedResidue b k n

theorem positionalDepthRefinement_reconstructs
    (b k n : ℕ) (hb : 0 < b) :
    (positionalDepthRefinement b k n).2 +
        placeValue b (k + 1) * (positionalDepthRefinement b k n).1 = n := by
  rw [← positionalDepthCoordinates_succ_eq_refinement]
  exact (positionalDecompositionAtDepth b (k + 1) n hb).1

theorem positionalDecompositionAtDepth_succ_reconstruction
    (b k n : ℕ) (hb : 0 < b) :
    residueAtDepth b (k + 1) n +
        placeValue b (k + 1) * quotientAtDepth b (k + 1) n = n := by
  exact (positionalDecompositionAtDepth b (k + 1) n hb).1

theorem refinedResidue_lt_placeValue_succ
    (b k n : ℕ) (hb : 0 < b) :
    refinedResidue b k n < placeValue b (k + 1) := by
  rw [← residueAtDepth_succ_eq_refinedResidue]
  exact (positionalDecompositionAtDepth b (k + 1) n hb).2

end CarrySelfAdjointOperator

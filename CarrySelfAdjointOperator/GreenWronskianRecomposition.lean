import CarrySelfAdjointOperator.DivisionFreeGreenConfinement
import Mathlib.Tactic

/-!
# Algebraic recomposition of completed Green channels

These identities isolate the bookkeeping required before any scalar
projection.  A multiplicative completion contributes two weighted Green
channels.  An additive synthesis contributes all diagonal and off-diagonal
pairs; the mixed terms are literal parts of the total Wronskian and cannot be
discarded.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

/-- Mixed Green term with the value/jet pair on the left channel tested
against the value/jet pair on the right channel. -/
def mixedGreenWronskian
    (F PsiF G PsiG : ℂ → ℂ) (z w : ℂ) : ℂ :=
  PsiF z * (starRingEnd ℂ) (G w) -
    F z * (starRingEnd ℂ) (PsiG w)

/-- The ordinary scalar Wronskian is the diagonal mixed term. -/
theorem mixedGreenWronskian_self
    (F Psi : ℂ → ℂ) (z w : ℂ) :
    mixedGreenWronskian F Psi F Psi z w =
      completedGreenWronskian F Psi z w :=
  rfl

/-- Boundary companion for a product `A * G` when `PsiX = -X'`:
`Psi(A G) = PsiA * G + A * PsiG`. -/
def productBoundaryCompanion
    (A PsiA G PsiG : ℂ → ℂ) (z : ℂ) : ℂ :=
  PsiA z * G z + A z * PsiG z

/-- Exact product rule for the division-free Green Wronskian.  It is the
algebraic source of the weighted direct-sum state
`G(z) a_z ⊕ A(z) g_z`. -/
theorem completedGreenWronskian_mul
    (A PsiA G PsiG : ℂ → ℂ) (z w : ℂ) :
    completedGreenWronskian
        (fun u ↦ A u * G u)
        (productBoundaryCompanion A PsiA G PsiG) z w =
      G z * (starRingEnd ℂ) (G w) *
          completedGreenWronskian A PsiA z w +
        A z * (starRingEnd ℂ) (A w) *
          completedGreenWronskian G PsiG z w := by
  simp only [completedGreenWronskian, productBoundaryCompanion,
    map_mul, map_add]
  ring

/-- At a zero of the second factor, the Green channel coming from the first
factor (for example the archimedean completion jet) vanishes identically.
Only the second-factor channel survives in the product decomposition.  This
records algebraically that multiplying a scalar characteristic by a
completion factor cannot use the completion jet to cancel an independent
provenance term at a zero of the scalar factor. -/
theorem completedGreenWronskian_mul_at_right_zero
    (A PsiA G PsiG : ℂ → ℂ) {z : ℂ} (hG : G z = 0) :
    completedGreenWronskian
        (fun u ↦ A u * G u)
        (productBoundaryCompanion A PsiA G PsiG) z z =
      A z * (starRingEnd ℂ) (A z) *
        completedGreenWronskian G PsiG z z := by
  rw [completedGreenWronskian_mul]
  simp [hG]

/-- If the second factor itself vanishes, its diagonal scalar Wronskian also
vanishes.  Thus the completed scalar Wronskian is zero, independently of the
first-factor jet; any surviving Green/provenance information must live before
scalar projection. -/
theorem completedGreenWronskian_mul_eq_zero_at_right_zero
    (A PsiA G PsiG : ℂ → ℂ) {z : ℂ} (hG : G z = 0) :
    completedGreenWronskian
        (fun u ↦ A u * G u)
        (productBoundaryCompanion A PsiA G PsiG) z z = 0 := by
  rw [completedGreenWronskian_mul_at_right_zero A PsiA G PsiG hG]
  simp [completedGreenWronskian, hG]

/-- Exact binary synthesis rule.  Besides the two diagonal Wronskians it
retains both off-diagonal channels. -/
theorem completedGreenWronskian_add
    (F PsiF G PsiG : ℂ → ℂ) (z w : ℂ) :
    completedGreenWronskian
        (fun u ↦ F u + G u)
        (fun u ↦ PsiF u + PsiG u) z w =
      mixedGreenWronskian F PsiF F PsiF z w +
        mixedGreenWronskian F PsiF G PsiG z w +
        mixedGreenWronskian G PsiG F PsiF z w +
        mixedGreenWronskian G PsiG G PsiG z w := by
  simp only [completedGreenWronskian, mixedGreenWronskian,
    map_add]
  ring

end

end CarrySelfAdjointOperator

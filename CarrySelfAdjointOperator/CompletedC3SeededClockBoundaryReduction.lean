import CarrySelfAdjointOperator.C3SeededClockTaylorTransport
import CarrySelfAdjointOperator.ProjectiveValveMomentFrontier
import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments
import Mathlib.Tactic

/-!
# Seeded C3 clock reduction of the polarized moment equation

The material C3 clock already satisfies the Hankel shift identity after the
full seed/gradient ledger is reconstructed to its four nodal values.  This
module records the exact consequence for the division-free polarized moment
equation.

The point is deliberately narrow.  The shift identity removes every interior
coefficient obligation.  For one block, and for every finite orthogonal atlas
of complete C3 blocks, the full two-variable coefficient equation is therefore
equivalent to its first-column boundary readout.

No calibration of that first column is asserted here.  In particular, the
known one-block zeroth-mass obstruction remains visible.  The intended next
step is to compare the atlas/completion first column with the already proved
bracket--TFVD Wronskian response coefficients, whose odd coefficients are the
canonical completed-native moments at every order.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator
namespace C3TraceDynamics

open CPFormal.Analytic.Cp

noncomputable section
set_option autoImplicit false

/-- Material-clock raw jet of one seeded reconstructed C3 block. -/
def seededClockMaterialRawJet
    (d a b c : ℝ) (x : SeededC3Data) (n : ℕ) : EuclideanSpace ℂ (Fin 4) :=
  seededRecover ((seededClock d a b c)^[n] x)

/-- Polarized coefficient read from one material-clock block. -/
def seededClockMaterialCoefficient
    (d a b c : ℝ) (x : SeededC3Data) (p q : ℕ) : ℂ :=
  inner ℂ (seededClockMaterialRawJet d a b c x p)
    (seededClockMaterialRawJet d a b c x q)

/-- The material clock discharges the complete interior shift obligation. -/
theorem seededClockMaterialCoefficient_shift
    (d a b c : ℝ) (x : SeededC3Data) (p q : ℕ) :
    seededClockMaterialCoefficient d a b c x p (q + 1) =
      seededClockMaterialCoefficient d a b c x (p + 1) q := by
  exact seededClock_inner_shift d a b c x x p q

/-- For one complete material-clock block, the full polarized coefficient
recurrence is equivalent to the first-column boundary identification. -/
theorem seededClockMaterialCoefficientEquation_iff_boundary
    (moments : ℕ → ℝ) (d a b c : ℝ) (x : SeededC3Data) :
    IsPolarizedGreenCoefficientEquation moments
        (seededClockMaterialCoefficient d a b c x) ↔
      ∀ p : ℕ,
        seededClockMaterialCoefficient d a b c x p 0 =
          oddMomentResponseCoefficient moments (p + 1) := by
  rw [polarizedGreenCoefficientEquation_iff_boundary_transport]
  constructor
  · exact fun h => h.1
  · intro hboundary
    exact ⟨hboundary, seededClockMaterialCoefficient_shift d a b c x⟩

/-- Native material-clock specialization on one complete C3 block. -/
def nativeSeededC3ClockMaterialRawJet
    (m : ℕ) (s : ℂ) (n : ℕ) : EuclideanSpace ℂ (Fin 4) :=
  seededClockMaterialRawJet
    (Real.log (3*m+1 : ℕ)) (Real.log (3*m+2 : ℕ))
    (Real.log (3*m+3 : ℕ)) (Real.log (3*m+4 : ℕ))
    (nativeBlockSeededData m s) n

/-- Native material coefficient of one complete C3 block. -/
def nativeSeededC3ClockMaterialCoefficient
    (m : ℕ) (s : ℂ) (p q : ℕ) : ℂ :=
  inner ℂ (nativeSeededC3ClockMaterialRawJet m s p)
    (nativeSeededC3ClockMaterialRawJet m s q)

/-- The native specialization inherits the shift identity without an extra
analytic or spectral premise. -/
theorem nativeSeededC3ClockMaterialCoefficient_shift
    (m : ℕ) (s : ℂ) (p q : ℕ) :
    nativeSeededC3ClockMaterialCoefficient m s p (q + 1) =
      nativeSeededC3ClockMaterialCoefficient m s (p + 1) q := by
  exact nativeSeededC3Clock_inner_shift m s p q

/-- Hence the complete native one-block moment equation has only one remaining
obligation: its first column. -/
theorem nativeSeededC3ClockMaterialCoefficientEquation_iff_boundary
    (moments : ℕ → ℝ) (m : ℕ) (s : ℂ) :
    IsPolarizedGreenCoefficientEquation moments
        (nativeSeededC3ClockMaterialCoefficient m s) ↔
      ∀ p : ℕ,
        nativeSeededC3ClockMaterialCoefficient m s p 0 =
          oddMomentResponseCoefficient moments (p + 1) := by
  rw [polarizedGreenCoefficientEquation_iff_boundary_transport]
  constructor
  · exact fun h => h.1
  · intro hboundary
    exact ⟨hboundary, nativeSeededC3ClockMaterialCoefficient_shift m s⟩

/-! ## Finite orthogonal atlas of complete material blocks -/

/-- Data of one seeded material block, including its four real material
frequencies. -/
structure SeededClockBlock where
  d : ℝ
  a : ℝ
  b : ℝ
  c : ℝ
  state : SeededC3Data

/-- Polarized coefficient of a finite orthogonal atlas.  Writing it as the
sum of the block Grams avoids choosing a second direct-sum carrier. -/
def seededClockAtlasCoefficient
    {ι : Type*} [Fintype ι]
    (block : ι → SeededClockBlock) (p q : ℕ) : ℂ :=
  ∑ i : ι,
    seededClockMaterialCoefficient
      (block i).d (block i).a (block i).b (block i).c (block i).state p q

/-- The material shift survives an arbitrary finite orthogonal atlas. -/
theorem seededClockAtlasCoefficient_shift
    {ι : Type*} [Fintype ι]
    (block : ι → SeededClockBlock) (p q : ℕ) :
    seededClockAtlasCoefficient block p (q + 1) =
      seededClockAtlasCoefficient block (p + 1) q := by
  unfold seededClockAtlasCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  exact seededClockMaterialCoefficient_shift
    (block i).d (block i).a (block i).b (block i).c (block i).state p q

/-- For every finite orthogonal material atlas, the entire division-free
polarized equation is equivalent to the boundary column.  Completion therefore
only has to calibrate the first column; the interior Hankel transport is
already forced by the native clock geometry. -/
theorem seededClockAtlasCoefficientEquation_iff_boundary
    {ι : Type*} [Fintype ι]
    (moments : ℕ → ℝ) (block : ι → SeededClockBlock) :
    IsPolarizedGreenCoefficientEquation moments
        (seededClockAtlasCoefficient block) ↔
      ∀ p : ℕ,
        seededClockAtlasCoefficient block p 0 =
          oddMomentResponseCoefficient moments (p + 1) := by
  rw [polarizedGreenCoefficientEquation_iff_boundary_transport]
  constructor
  · exact fun h => h.1
  · intro hboundary
    exact ⟨hboundary, seededClockAtlasCoefficient_shift block⟩

/-- The scalar target of the remaining boundary column is already fixed by the
completed bracket--TFVD Wronskian: its odd response coefficients are exactly
the canonical native moments. -/
theorem canonicalTfvdOddResponseCoefficient_eq_nativeBoundaryTarget
    (M n : ℕ) :
    canonicalC3BracketTfvdResponseTaylorCoefficient M (2 * n + 1) =
      oddMomentResponseCoefficient
        canonicalCompletedNativeLogDerivativeMoment (2 * n + 1) := by
  rw [canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
    oddMomentResponseCoefficient_odd]

/-- Even boundary indices vanish by parity. -/
theorem completedResponseEvenBoundaryTarget_zero
    (n : ℕ) :
    oddMomentResponseCoefficient
      canonicalCompletedNativeLogDerivativeMoment (2 * n) = 0 := by
  exact oddMomentResponseCoefficient_even _ _

end
end C3TraceDynamics
end CarrySelfAdjointOperator

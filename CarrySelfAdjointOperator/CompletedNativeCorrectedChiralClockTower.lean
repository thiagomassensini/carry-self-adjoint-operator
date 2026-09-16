import CarrySelfAdjointOperator.CompletedNativeCorrectedCausalChiralGate
import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import Mathlib.Tactic

/-!
# Corrected native chiral clock tower

The finite `SeededClockBlock` carrier is a positive atomic Gram object.  The
completed native chiral boundary readout, by contrast, is obtained from the
signed `(+1,-1)` chiral signature.  This file therefore does not force the
signed readout into a finite positive material block.

Instead it constructs the equivalent canonical two-index native clock tower
directly from the already identified completed-native moment sequence.  Its
interior transport is the division-free Green/Hankel shift, and its first
column is exactly the corrected native chiral boundary coefficient at every
order.

This closes the boundary calibration at the coefficient-tower level without
introducing a new positivity hypothesis, Hankel fit, Jacobi reconstruction, or
an assumed same-edge material transport.  A finite seeded-clock atlas can still
be used whenever its existing same-edge transport is available; an equivalence
with the corrected boundary formulation is recorded below.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics

noncomputable section

/-- A two-index coefficient carrier has corrected native chiral boundary
transport when its first column is the canonical corrected chiral readout. -/
def HasCorrectedNativeChiralBoundaryTransport
    (M : ℕ) (coeff : ℕ → ℕ → ℂ) : Prop :=
  ∀ p : ℕ,
    coeff p 0 =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p

/-- The canonical corrected native clock tower.  It is the unique coefficient
array selected by the completed-native moment sequence and the division-free
polarized Green recurrence. -/
def canonicalCompletedNativeCorrectedClockTowerCoefficient
    (p q : ℕ) : ℂ :=
  polarizedGreenMomentCoefficient
    canonicalCompletedNativeLogDerivativeMoment p q

/-- Every entry of the native clock tower is already the corrected chiral
coefficient on the same total-degree diagonal. -/
theorem canonicalCompletedNativeCorrectedClockTowerCoefficient_eq_correctedChiralBoundaryCoefficient
    (M p q : ℕ) :
    canonicalCompletedNativeCorrectedClockTowerCoefficient p q =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M (p + q) := by
  unfold canonicalCompletedNativeCorrectedClockTowerCoefficient
  exact
    (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_polarizedMoment
      M p q).symm

/-- In particular, the first column has the required corrected native chiral
boundary transport, with no auxiliary transport hypothesis. -/
theorem canonicalCompletedNativeCorrectedClockTower_hasCorrectedNativeChiralBoundaryTransport
    (M : ℕ) :
    HasCorrectedNativeChiralBoundaryTransport M
      canonicalCompletedNativeCorrectedClockTowerCoefficient := by
  intro p
  simpa using
    (canonicalCompletedNativeCorrectedClockTowerCoefficient_eq_correctedChiralBoundaryCoefficient
      M p 0)

/-- The canonical corrected tower satisfies the complete division-free
polarized Green coefficient equation. -/
theorem canonicalCompletedNativeCorrectedClockTower_coefficientEquation :
    IsPolarizedGreenCoefficientEquation
      canonicalCompletedNativeLogDerivativeMoment
      canonicalCompletedNativeCorrectedClockTowerCoefficient := by
  change IsPolarizedGreenCoefficientEquation
    canonicalCompletedNativeLogDerivativeMoment
    (polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment)
  exact polarizedGreenMomentCoefficient_coefficientEquation
    canonicalCompletedNativeLogDerivativeMoment

/-- Hence the native clock tower transports coefficients diagonally through the
interior exactly as the material seeded clock does. -/
theorem canonicalCompletedNativeCorrectedClockTower_shift
    (p q : ℕ) :
    canonicalCompletedNativeCorrectedClockTowerCoefficient p (q + 1) =
      canonicalCompletedNativeCorrectedClockTowerCoefficient (p + 1) q := by
  exact polarizedGreenCoefficient_transport
    canonicalCompletedNativeCorrectedClockTower_coefficientEquation p q

/-- Packaged corrected native clock tower.  The first field is the actual
coefficient array; the other fields certify the interior and boundary laws. -/
structure CorrectedNativeClockTower (M : ℕ) where
  coefficient : ℕ → ℕ → ℂ
  coefficientEquation :
    IsPolarizedGreenCoefficientEquation
      canonicalCompletedNativeLogDerivativeMoment coefficient
  boundaryTransport :
    HasCorrectedNativeChiralBoundaryTransport M coefficient

/-- Canonical realization of the corrected native clock tower. -/
def canonicalCompletedNativeCorrectedClockTower
    (M : ℕ) : CorrectedNativeClockTower M where
  coefficient := canonicalCompletedNativeCorrectedClockTowerCoefficient
  coefficientEquation :=
    canonicalCompletedNativeCorrectedClockTower_coefficientEquation
  boundaryTransport :=
    canonicalCompletedNativeCorrectedClockTower_hasCorrectedNativeChiralBoundaryTransport M

/-- Any corrected native clock tower inherits the Green diagonal shift from its
coefficient equation. -/
theorem CorrectedNativeClockTower.shift
    {M : ℕ} (tower : CorrectedNativeClockTower M) (p q : ℕ) :
    tower.coefficient p (q + 1) = tower.coefficient (p + 1) q := by
  exact polarizedGreenCoefficient_transport tower.coefficientEquation p q

/-- The division-free equation makes every corrected native clock tower equal
to the canonical moment tower entry-by-entry.  Thus the construction is not an
extra choice of tower. -/
theorem CorrectedNativeClockTower.coefficient_eq_canonical
    {M : ℕ} (tower : CorrectedNativeClockTower M) (p q : ℕ) :
    tower.coefficient p q =
      canonicalCompletedNativeCorrectedClockTowerCoefficient p q := by
  simpa [canonicalCompletedNativeCorrectedClockTowerCoefficient] using
    (polarizedGreenCoefficient_unique tower.coefficientEquation p q)

/-- The packaged canonical tower exposes the corrected chiral first column
directly. -/
theorem canonicalCompletedNativeCorrectedClockTower_firstColumn
    (M p : ℕ) :
    (canonicalCompletedNativeCorrectedClockTower M).coefficient p 0 =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p := by
  exact
    (canonicalCompletedNativeCorrectedClockTower M).boundaryTransport p

/-! ## Compatibility with the existing finite seeded-clock atlas -/

/-- Existing same-edge Green-to-clock transport implies the corrected native
chiral boundary formulation. -/
theorem seededClockAtlas_hasCorrectedNativeChiralBoundaryTransport_of_sameEdgeTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block) :
    HasCorrectedNativeChiralBoundaryTransport M
      (seededClockAtlasCoefficient block) := by
  intro p
  exact
    seededClockAtlasCoefficient_firstColumn_eq_correctedNativeChiralBoundaryCoefficient_of_sameEdgeTransport
      M block p htransport

/-- Conversely, corrected native chiral boundary transport is exactly the old
same-edge Wronskian boundary calibration for a finite seeded-clock atlas. -/
theorem seededClockAtlas_sameEdgeTransport_of_hasCorrectedNativeChiralBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M
      (seededClockAtlasCoefficient block)) :
    HasSameEdgeGreenToClockBoundaryTransport M block := by
  intro p
  calc
    seededClockAtlasCoefficient block p 0 =
        canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p :=
      htransport p
    _ = canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
          M (p + 1) :=
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_response M p

/-- For a finite seeded-clock atlas, the corrected transport predicate is not a
new assumption: it is equivalent to the already isolated same-edge transport. -/
theorem seededClockAtlas_hasCorrectedNativeChiralBoundaryTransport_iff_sameEdgeTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) :
    HasCorrectedNativeChiralBoundaryTransport M
        (seededClockAtlasCoefficient block) ↔
      HasSameEdgeGreenToClockBoundaryTransport M block := by
  constructor
  · exact
      seededClockAtlas_sameEdgeTransport_of_hasCorrectedNativeChiralBoundaryTransport
        M block
  · exact
      seededClockAtlas_hasCorrectedNativeChiralBoundaryTransport_of_sameEdgeTransport
        M block

end

end CarrySelfAdjointOperator

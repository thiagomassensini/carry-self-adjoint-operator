import CarrySelfAdjointOperator.PrimeDepthAllOrderMomentBridge
import CarrySelfAdjointOperator.CompletedNativeHPGateAudit
import CarrySelfAdjointOperator.CompletedNativeCausalCoefficientMomentGate
import Mathlib.Tactic

/-!
# Six-source TFVD center--leg bridge

The enriched six-source material clock already supplies the complete
two-index polarized coefficient array.  This file does not replace that
array by a raw seeded-clock Gram.  Instead, it records the remaining bridge
to the concrete BR2 projective Hilbert carrier as one explicit entrywise
defect.

The first summand of the defect is the coefficient read from the lossless
six-source TFVD reconstruction (and therefore retains the completed Green
ports, provenance, off-diagonal, residual, head--tail, and chart channels).
The second summand is the inner product of the independently constructed
projective incidence jet.  The two are equal exactly when the center--leg
readout required by the existing HP interface holds.

No positivity, Gram factorization, or carrier is defined from the moment
matrices in this file.
-/

open scoped InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The scalar coefficient obtained from the full enriched six-source TFVD
ledger at a pair of polarized orders.  This is only a named view of the
already proved material tower; it does not scalarize the source before the
completed ledger has been synthesized. -/
abbrev nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (p r : ℕ) : ℂ :=
  nativeC3SeededClockTfvdSixSourceTowerCoefficient M q hq0 hq1 S p r

/-- The material six-source coefficient is the canonical polarized Green
coefficient in every bidegree.  This transports all completed channels as a
single provenance-preserving equality, before any Hilbert pairing is used. -/
theorem nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_polarizedGreenMomentCoefficient
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (p r : ℕ) :
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hqpos.le hq1 S p r =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p r := by
  exact polarizedGreenCoefficient_unique
    (nativeC3SeededClockTfvdSixSourceTower_coefficientEquation
      M q hqpos hq1 S) p r

/-- The sole remaining center--leg seam.  It compares the fully synthesized
six-source coefficient with the inner product of the already injective BR2
projective-incidence jet. -/
def nativeC3SeededClockTfvdSixSourceCenterLegDefect
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) (i j : ℕ ⊕ ℕ) : ℂ :=
  nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
      M q hq0 hq1 S (parityJetNumber i) (parityJetNumber j) -
    inner ℂ (br2CameraBracketProjectiveHilbertParityJet base radius i)
      (br2CameraBracketProjectiveHilbertParityJet base radius j)

/-- After the proven six-source tower identification, the defect contains no
unresolved moment or shift term: it is exactly the difference between the
canonical polarized coefficient and the projective Hilbert pairing. -/
theorem nativeC3SeededClockTfvdSixSourceCenterLegDefect_eq_polarizedResidual
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) (i j : ℕ ⊕ ℕ) :
    nativeC3SeededClockTfvdSixSourceCenterLegDefect
        M q hqpos.le hq1 S base radius i j =
      polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment
          (parityJetNumber i) (parityJetNumber j) -
        inner ℂ (br2CameraBracketProjectiveHilbertParityJet base radius i)
          (br2CameraBracketProjectiveHilbertParityJet base radius j) := by
  unfold nativeC3SeededClockTfvdSixSourceCenterLegDefect
  rw [nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_polarizedGreenMomentCoefficient
    M q hqpos hq1 S]

/-- In the concrete carrier expected by the HP gate, the center--leg readout
is equivalent to vanishing of the explicit six-source defect on the already
off-diagonal center--leg samples.  This is the smallest remaining theorem:
all source-to-coefficient and all incidence-to-independence transports have
already been discharged. -/
theorem nativeC3SeededClockTfvdSixSource_centerLegReadout_iff_defect_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) (incidence : BR2CameraIncidence) :
    HasCanonicalCompletedNativeTfvdGreenCenterLegReadout incidence
        (br2CameraBracketProjectiveHilbertParityJet base radius) ↔
      ∀ i j : ℕ ⊕ ℕ,
        incidence.centerCoordinate i ≠ incidence.legCoordinate j →
          nativeC3SeededClockTfvdSixSourceCenterLegDefect
            M q hqpos.le hq1 S base radius i j = 0 := by
  constructor
  · intro hreadout i j hij
    rw [nativeC3SeededClockTfvdSixSourceCenterLegDefect_eq_polarizedResidual
      M q hqpos hq1 S base radius i j]
    exact sub_eq_zero.mpr (hreadout i j hij)
  · intro hdefect i j hij
    have hzero := hdefect i j hij
    rw [nativeC3SeededClockTfvdSixSourceCenterLegDefect_eq_polarizedResidual
      M q hqpos hq1 S base radius i j] at hzero
    exact sub_eq_zero.mp hzero

/-! ## Low-order orientation and parity checks -/

/-- The even/even origin has the canonical zeroth moment on the material
side of the defect. -/
theorem nativeC3SeededClockTfvdSixSourceCenterLegDefect_even_zero_even_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ) :
    nativeC3SeededClockTfvdSixSourceCenterLegDefect
        M q hqpos.le hq1 S base radius (Sum.inl 0) (Sum.inl 0) =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) -
        inner ℂ
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0))
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0)) := by
  unfold nativeC3SeededClockTfvdSixSourceCenterLegDefect
  change nativeC3SeededClockTfvdSixSourceTowerCoefficient
      M q hqpos.le hq1 S 0 0 - _ = _
  rw [(nativeC3SeededClockTfvdSixSourceTower_coefficientEquation
    M q hqpos hq1 S).coeff_zero_zero]

/-- The odd/odd origin has the first shifted canonical moment on the
material side of the defect. -/
theorem nativeC3SeededClockTfvdSixSourceCenterLegDefect_odd_zero_odd_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ) :
    nativeC3SeededClockTfvdSixSourceCenterLegDefect
        M q hqpos.le hq1 S base radius (Sum.inr 0) (Sum.inr 0) =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) -
        inner ℂ
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inr 0))
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inr 0)) := by
  unfold nativeC3SeededClockTfvdSixSourceCenterLegDefect
  change nativeC3SeededClockTfvdSixSourceTowerCoefficient
      M q hqpos.le hq1 S 1 1 - _ = _
  rw [(nativeC3SeededClockTfvdSixSourceTower_coefficientEquation
    M q hqpos hq1 S).coeff_one_one]

/-- The first mixed pair has zero material coefficient.  Thus any nonzero
mixed defect is visible directly as a Green-orientation/pairing mismatch. -/
theorem nativeC3SeededClockTfvdSixSourceCenterLegDefect_even_zero_odd_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ) :
    nativeC3SeededClockTfvdSixSourceCenterLegDefect
        M q hqpos.le hq1 S base radius (Sum.inl 0) (Sum.inr 0) =
      - inner ℂ
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0))
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inr 0)) := by
  unfold nativeC3SeededClockTfvdSixSourceCenterLegDefect
  change nativeC3SeededClockTfvdSixSourceTowerCoefficient
      M q hqpos.le hq1 S 0 1 - _ = _
  rw [(nativeC3SeededClockTfvdSixSourceTower_coefficientEquation
    M q hqpos hq1 S).coeff_zero_one]
  ring

/-- The next even/even entry has the first shifted canonical moment.  This
checks that the material total-degree convention uses `p + q`, rather than a
translated clock-cell index. -/
theorem nativeC3SeededClockTfvdSixSourceCenterLegDefect_even_one_even_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ) :
    nativeC3SeededClockTfvdSixSourceCenterLegDefect
        M q hqpos.le hq1 S base radius (Sum.inl 1) (Sum.inl 0) =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) -
        inner ℂ
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 1))
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0)) := by
  unfold nativeC3SeededClockTfvdSixSourceCenterLegDefect
  change nativeC3SeededClockTfvdSixSourceTowerCoefficient
      M q hqpos.le hq1 S 2 0 - _ = _
  rw [polarizedGreenCoefficient_unique
    (nativeC3SeededClockTfvdSixSourceTower_coefficientEquation
      M q hqpos hq1 S) 2 0]
  simp [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

end

end CarrySelfAdjointOperator

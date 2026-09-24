import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceCameraPromotionAudit
import Mathlib.Tactic

/-!
# Functional six-source symplectic vector kernel

The native six-source corrected boundary already has a vector realization
before its scalar Green readout.  This file exposes that realization at every
finite cutoff: reconstruct the direct and reflected Green ports from the six
separated TFVD analyses, promote each port to the realified Naimark carrier,
and retain the quarter-turn of the reflected port as a third vector.

The resulting complex kernel is read through two *skew* real quadratures.  It
therefore realizes the corrected Green kernel exactly, but it is deliberately
not called a positive Hilbert Gram.  The missing step for Route B remains a
provenance-preserving map from this realified Naimark triple into the finite
`CarryVerticalL2` camera family on which the historical Parseval readout acts.

No moment, Hankel matrix, positivity, or incidence lift is used here.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-! ## The pre-scalar vector family -/

/-- The three Naimark vectors retained before the two real Green skew
quadratures are evaluated: direct, reflected, and quarter-turned reflected.
This is an alias for the existing Hilbert triple used by the four-trace
bridge; unlike its fixed-cutoff presentation, the source below is available
at arbitrary finite cutoff. -/
abbrev CanonicalC3SixSourceSymplecticNaimarkVectorCarrier :=
  CanonicalC3SixCameraSymplecticGreenCarrierHilbert

/-- Promote the direct/reflected ports recovered from six separated TFVD
analyses to the three-vector realified Naimark carrier.  The source roles are
not enumerated as camera slots: the ports are first recovered by the existing
provenance-aware six-source reconstruction. -/
def canonicalC3SixSourceSymplecticNaimarkVector
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    CanonicalC3SixSourceSymplecticNaimarkVectorCarrier :=
  let ports := canonicalC3SixSourceRecoveredGreenPorts M z w q hq0 hq1 S data
  WithLp.toLp 2
    (finiteC3SymplecticNaimarkRealization (3 * M) ports.1,
      WithLp.toLp 2
        (finiteC3SymplecticNaimarkRealization (3 * M) ports.2,
          finiteC3SymplecticNaimarkRealization (3 * M)
            (Complex.I • ports.2)))

/-- Retain the direct and quarter-turned Green skew readings separately. -/
def canonicalC3SixSourceSymplecticNaimarkQuadratures
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    FiniteC3SymplecticGreenQuadratures :=
  (canonicalC3SixSourceSymplecticNaimarkVector
    M z w q hq0 hq1 S data).quadratures

/-- Complex corrected-kernel readout of the two retained skew quadratures. -/
def canonicalC3SixSourceSymplecticNaimarkReadout
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) : ℂ :=
  (canonicalC3SixSourceSymplecticNaimarkQuadratures
    M z w q hq0 hq1 S data).complexReadout

/-- The direct Naimark coordinate is the promotion of the direct recovered
six-source Green port, before every scalar pairing. -/
theorem canonicalC3SixSourceSymplecticNaimarkVector_direct
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    (canonicalC3SixSourceSymplecticNaimarkVector
      M z w q hq0 hq1 S data).direct =
      finiteC3SymplecticNaimarkRealization (3 * M)
        (canonicalC3SixSourceRecoveredGreenPorts
          M z w q hq0 hq1 S data).1 :=
  rfl

/-- The reflected Naimark coordinate is likewise retained independently. -/
theorem canonicalC3SixSourceSymplecticNaimarkVector_reflected
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    (canonicalC3SixSourceSymplecticNaimarkVector
      M z w q hq0 hq1 S data).reflected =
      finiteC3SymplecticNaimarkRealization (3 * M)
        (canonicalC3SixSourceRecoveredGreenPorts
          M z w q hq0 hq1 S data).2 :=
  rfl

/-- The third coordinate is a literal quarter-turn of the retained reflected
port, not a scalar imaginary-part operation. -/
theorem canonicalC3SixSourceSymplecticNaimarkVector_quarterTurnReflected
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    (canonicalC3SixSourceSymplecticNaimarkVector
      M z w q hq0 hq1 S data).quarterTurnReflected =
      finiteC3SymplecticNaimarkRealization (3 * M)
        (Complex.I • (canonicalC3SixSourceRecoveredGreenPorts
          M z w q hq0 hq1 S data).2) :=
  rfl

/-- Exact functional kernel identity: the scalar corrected six-source
boundary is the lossless two-quadrature readout of the pre-scalar Naimark
vector family.  The right side is a Green/symplectic polarization, not a
positive Hilbert Gram. -/
theorem canonicalC3SixSourceSymplecticNaimarkReadout_eq_correctedBoundary
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3SixSourceSymplecticNaimarkReadout
      M z w q hq0 hq1 S data =
      canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary
        M z w q hq0 hq1 S data := by
  change (finiteC3SymplecticNaimarkGreenQuadratures (3 * M)
      (canonicalC3SixSourceRecoveredGreenPorts M z w q hq0 hq1 S data).1
      (canonicalC3SixSourceRecoveredGreenPorts M z w q hq0 hq1 S data).2).complexReadout = _
  exact finiteC3SymplecticNaimark_complexReadout_eq_greenForm _ _ _

/-! ## Native functional specialization -/

/-- The same vector family at the native material six-source.  Its parameters
remain global `(z,w)` while the recovered ports retain their explicit
operator-height provenance. -/
def nativeC3SeededClockTfvdSixSourceSymplecticNaimarkVector
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    CanonicalC3SixSourceSymplecticNaimarkVectorCarrier :=
  canonicalC3SixSourceSymplecticNaimarkVector M
    (operatorHeightParameter z) (operatorHeightParameter w)
    q hq0 hq1 S
    (nativeC3SeededClockTfvdSixSourceAnalysis M q S
      (operatorHeightParameter z) (operatorHeightParameter w))

/-- Native two-quadrature readout, still prior to the moment identification. -/
def nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℂ :=
  canonicalC3SixSourceSymplecticNaimarkReadout M
    (operatorHeightParameter z) (operatorHeightParameter w)
    q hq0 hq1 S
    (nativeC3SeededClockTfvdSixSourceAnalysis M q S
      (operatorHeightParameter z) (operatorHeightParameter w))

/-- The native corrected six-source kernel is exactly the pre-moment,
two-quadrature Naimark readout. -/
theorem nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout_eq_correctedBoundary
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout
      M z w q hq0 hq1 S =
      nativeC3SeededClockTfvdSixSourceCorrectedBoundary
        M z w q hq0 hq1 S :=
  canonicalC3SixSourceSymplecticNaimarkReadout_eq_correctedBoundary
    M (operatorHeightParameter z) (operatorHeightParameter w)
    q hq0 hq1 S
    (nativeC3SeededClockTfvdSixSourceAnalysis M q S
      (operatorHeightParameter z) (operatorHeightParameter w))

/-- This identifies the native functional Naimark readout with the existing
radial ledger coordinate without passing through moments or a Hankel matrix. -/
theorem nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout_eq_ledgerRadial
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout
      M z w q hqpos.le hq1 S =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).radialComplexReadout := by
  rw [nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout_eq_correctedBoundary,
    nativeC3SeededClockTfvdSixSourceCorrectedBoundary_eq_ledgerRadial
      M z w q hqpos hq1 S]

/-! ## The full vector ledger before the final scalar readout -/

/-- The native one-point slice of the realified Naimark triple.  This is the
vector family that would have to be differentiated (in an appropriate
realified vector calculus) before it could supply an incidence lift by jets.
It intentionally has not been defined from coefficients or moments. -/
def nativeC3SeededClockTfvdSixSourceOnePointSymplecticNaimarkVector
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (z : ℂ) :
    CanonicalC3SixSourceSymplecticNaimarkVectorCarrier :=
  nativeC3SeededClockTfvdSixSourceSymplecticNaimarkVector
    (M + 1) z 0 q hq0 hq1 S

/-- The complete all-channel vector state before the native final scalar
readout.  It retains the Naimark triple together with structural provenance,
tail, xi-weight, and archimedean-chart coordinates. -/
def nativeC3SeededClockTfvdSixSourceKernelLedgerVector
    (M : ℕ) (z w : ℂ) :
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert :=
  canonicalCompletedC3AllCutoffKernelLedgerState M z w

/-- The radial coordinate of the full native ledger is exactly the readout of
the independently retained three-vector Naimark family. -/
theorem nativeC3SeededClockTfvdSixSourceKernelLedgerVector_radial_eq_symplecticNaimark
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (nativeC3SeededClockTfvdSixSourceKernelLedgerVector
      M z w).radialComplexReadout =
      nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout
        M z w q hqpos.le hq1 S := by
  exact (nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout_eq_ledgerRadial
    M z w q hqpos hq1 S).symm

/-- The final native scalar readout is applied only after the full ledger
coordinates have been retained.  This is a scalar equality; it does not turn
the preceding Green/symplectic coordinate into a positive Gram. -/
theorem nativeC3SeededClockTfvdSixSourceKernelLedgerVector_final_eq_nativeFinalReadout
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (nativeC3SeededClockTfvdSixSourceKernelLedgerVector
      M z w).finalReadout =
      nativeC3SeededClockTfvdSixSourceFinalReadout
        M z w q hqpos.le hq1 S := by
  exact (nativeC3SeededClockTfvdSixSourceFinalReadout_eq_ledger
    M z w q hqpos hq1 S).symm

/-! ## The remaining positive-camera seam -/

/-- Exact missing type-level arrow.  It must be a non-separable,
provenance-preserving real-linear promotion: the source is the three-vector
symplectic Naimark state above, while the target is precisely the finite
vertical Hilbert family accepted by the historical Parseval camera.  No such
map is supplied by the existing realification/Naimark bridges. -/
abbrev CanonicalC3SymplecticNaimarkToFiniteCameraFamily :=
  CanonicalC3SixSourceSymplecticNaimarkVectorCarrier →ₗ[ℝ]
    FiniteHilbertFamily CanonicalC3SixCameraSlot
      CanonicalCompletedTfvdGreenHilbertCarrier

end

end CarrySelfAdjointOperator

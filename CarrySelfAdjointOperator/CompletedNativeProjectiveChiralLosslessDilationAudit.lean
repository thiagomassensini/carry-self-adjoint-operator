import CarrySelfAdjointOperator.CompletedNativeAmbientRadialIntertwiningNoGo
import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralCarrier
import CarrySelfAdjointOperator.CompletedNativeChiralReturnStorage
import CarrySelfAdjointOperator.CompletedC3CausalChiralPolarizedAudit
import CarrySelfAdjointOperator.CompletedC3CausalChiralKernelObstruction
import CarrySelfAdjointOperator.DiscreteProjectiveReconstruction
import CarrySelfAdjointOperator.CompletedC3ValveNaturality
import Mathlib.Tactic

/-!
# Audit of native projective/chiral lossless-dilation candidates

This is an audit module, deliberately not a new positivity construction.
The carrier statuses used here are:

| carrier or transformation | status |
|---|---|
| literal BR2 | NO-GO |
| literal Gamma | NO-GO |
| literal normalized ambient Gram | NO-GO |
| projective/chiral lossless defect channel | OPEN |

The existing native projective transformation is the graph
`v ↦ (v, q v)`, with the exact positive Hermite--Biehler amplitude restored
afterwards.  Its second coordinate is therefore already the requested first
output `q v`; it is not a further defect coordinate.  The graph carrier is
only a product type, not a supplied Hilbert direct sum.  Its natural
coordinatewise *sum* form adds the two energies, whereas `dslope` and Pick
arise from the separately defined *signed* difference form.  Thus treating
the existing second coordinate as a lossless defect would be circular.

The closest existing two-output geometric construction is the C3
coisometric block

`sqrt(2 Im z) ambientResponse(z) ⊕ negativeChirality(z)`.

Its negative chiral coordinate is the projective `q` output, while the first
coordinate is the only geometrically supplied prospective loss channel.  The
polarized residual below records exactly why it does not close: on the
diagonal it is the literal normalized-ambient mismatch already ruled out by
the ambient no-go.  On the full causal source span an even stronger,
independent finite-rank obstruction rules out the proposed fixed-parameter
coisometric contraction.

`DiscreteProjectiveReconstruction` and `CompletedC3ValveNaturality` were also
audited.  They provide exact boundary-plus-mass reconstruction and
multiplicative projective-mass identities, respectively, but no Hilbert
second output, no polarized inner-product conservation law, and no map whose
first Hilbert output is `q v`.

Consequently this module does not use a square root of `I - T* T`, a
Kolmogorov/RKHS factorization, Cholesky, Pick PSD, Stieltjes positivity, or a
Jacobi/spectral conclusion.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace MatrixOrder

namespace CarrySelfAdjointOperator

noncomputable section

/-! ## The existing projective graph is not a defect dilation -/

/-- Coordinatewise positive form of the existing unweighted projective
graph.  It is recorded explicitly because the graph carrier itself is not
equipped in the repository with a Hilbert direct-sum structure. -/
def canonicalCompletedNativeProjectiveChiralGraphSumForm
    (u v : CanonicalCompletedNativeProjectiveChiralCarrier) : ℂ :=
  inner ℂ u.1 v.1 + inner ℂ u.2 v.2

/-- The coordinatewise sum form adds the incident and returned energies;
only the separate projective signed form subtracts.  This makes precise that
the graph's second coordinate is the transported output `q v`, not an
independently supplied defect state. -/
theorem canonicalCompletedNativeProjectiveChiralGraphSumForm_defectState_eq_add
    (k i j : ℕ) :
    canonicalCompletedNativeProjectiveChiralGraphSumForm
        (canonicalCompletedNativeRadialChiralDefectState k i)
        (canonicalCompletedNativeRadialChiralDefectState k j) =
      inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) +
        inner ℂ (completedNativeRadialChiralMultiplierState k i)
          (completedNativeRadialChiralMultiplierState k j) := by
  rfl

/-- The exact residual left by the graph transformation.  It is a difference
of the incident and returned Cauchy Grams, not an independently realized Gram
of a second output. -/
def canonicalCompletedNativeRadialChiralGraphDefectResidual
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N

/-- The graph residual is exactly the native radial Pick matrix. -/
theorem canonicalCompletedNativeRadialChiralGraphDefectResidual_eq_pick
    (k N : ℕ) :
    canonicalCompletedNativeRadialChiralGraphDefectResidual k N =
      canonicalCompletedNativeRadialChiralPickSampleMatrix k N := by
  exact (canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect
    k N).symm

/-- Positivity of the graph residual is exactly finite-family contractivity
of the very multiplier whose defect is being sought.  Hence this residual
cannot be turned into a Gram by the current graph data without first closing
the Pick gate. -/
theorem canonicalCompletedNativeRadialChiralGraphDefectResidual_posSemidef_iff
    (k N : ℕ) :
    (canonicalCompletedNativeRadialChiralGraphDefectResidual k N).PosSemidef ↔
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k N := by
  rw [canonicalCompletedNativeRadialChiralGraphDefectResidual,
    ← canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect]
  exact (canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
    k N).symm

/-- The one-point graph residual is eventually contractive for the genuine
central reason `h₀ > 0`.  This is a diagnostic for the signed residual, not a
construction of a defect vector. -/
theorem canonicalCompletedNativeRadialChiralGraphResidual_one_eventually_contractive :
    ∀ᶠ k : ℕ in Filter.atTop,
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k 1 :=
  canonicalCompletedNativeRadialChiralMultiplierContractiveAt_one_eventually_of_moment_zero_pos
    canonicalCompletedNativeLogDerivativeMoment_zero_pos

/-- The existing certified two-point result controls the graph residual on
all two-point linear combinations.  It remains an audit result: it does not
define a third, loss-channel output. -/
theorem canonicalCompletedNativeRadialChiralGraphResidual_two_eventually_contractive :
    ∀ᶠ k : ℕ in Filter.atTop,
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k 2 :=
  canonicalCompletedNativeChiralTwoPoint_contractive_eventually

/-! ## Best existing geometric two-output candidate and its residual -/

/-- Residual of the closest native geometric two-output candidate.  Its
input is the positive Wronskian chirality and its output block retains the
negative (`q`) chirality together with the scaled ambient coordinate.  A
lossless dilation would make this residual vanish. -/
def canonicalCompletedC3CoisometricChiralDilationResidual
    (M : ℕ) (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3NormalizedCoisometricChiralKernel M z w hzHalf hwHalf -
    canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel M z w

/-- Exact polarized residual of the coisometric candidate.  It is the sum of
the ambient provenance channel and a chiral cross/separation channel; it is
not a lone defect Gram. -/
theorem canonicalCompletedC3CoisometricChiralDilationResidual_eq
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3CoisometricChiralDilationResidual
        M z w hzStrip.1 hwStrip.1 =
      (((Real.sqrt (2 * z.im) : ℝ) : ℂ) *
          ((Real.sqrt (2 * w.im) : ℝ) : ℂ)) *
        canonicalCompletedC3NormalizedAmbientResponseKernel
          z w hzStrip.1 hwStrip.1 +
      Complex.I * (w - conj z) *
        canonicalCompletedNativePolarizedDslopeKernel z w := by
  exact canonicalCompletedC3NormalizedCoisometricChiralKernel_sub_positive_eq
    M hzStrip hwStrip hzF hwF hsep

/-- On the diagonal the same residual is precisely the scaled normalized
ambient-minus-`dslope` kernel mismatch.  This identifies it as an ambient
provenance residual rather than a new projective loss channel. -/
theorem canonicalCompletedC3CoisometricChiralDilationResidual_diagonal_eq
    (M : ℕ) {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    canonicalCompletedC3CoisometricChiralDilationResidual
        M z z hzStrip.1 hzStrip.1 =
      ((2 * z.im : ℝ) : ℂ) *
        (canonicalCompletedC3NormalizedAmbientResponseKernel
            z z hzStrip.1 hzStrip.1 -
          canonicalCompletedNativePolarizedDslopeKernel z z) := by
  exact canonicalCompletedC3NormalizedCoisometricChiralKernel_diagonal_sub_positive_eq
    M hzStrip hzF hzIm

/-- The literal ambient component used by the coisometric candidate is now
closed globally: its normalized radial boundary intertwining is impossible.
This is intentionally a guardrail against recycling that component as an
unexplained defect channel. -/
theorem not_canonicalCompletedC3CoisometricCandidate_literalAmbientIntertwining :
    ¬ CanonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining :=
  not_canonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining

/-- Stronger independent stop: the natural fixed-parameter causal
coisometric candidate cannot even satisfy its required defect-Gram
contraction on the actual causal source span in the open upper half-plane.
The obstruction is finite-rank/kernel incompatibility, not a Pick or moment
positivity argument. -/
theorem not_canonicalCompletedC3CausalCoisometricCandidateDefectGram_of_im_pos
    (z : ℂ) (hzIm : 0 < z.im) :
    ¬ CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z :=
  not_canonicalCompletedC3CausalChiralDefectGramNonnegativeAt_of_im_pos z hzIm

/-! ## Explicit all-order frontier -/

/-- The all-order frontier left after the audit: the graph residual becomes a
positive Gram exactly when the native chiral multiplier is contractive on all
finite radial families.  This is a named equivalence, not a new positivity
claim. -/
theorem canonicalCompletedNativeProjectiveChiralLosslessFrontier_iff :
    CanonicalCompletedNativeRadialProjectiveChiralEventuallyPosSemidefinite ↔
      CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive :=
  canonicalCompletedNativeRadialProjectiveChiralEventuallyPosSemidefinite_iff_contractive

end

end CarrySelfAdjointOperator

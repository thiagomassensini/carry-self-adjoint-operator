import CarrySelfAdjointOperator.NaturalNativeSourceValveGreenProvenance
import CarrySelfAdjointOperator.ProjectiveValveMomentFrontier
import Mathlib.Tactic

/-!
# The native shift which forces the height operator

This file exposes the pre-Hankel identity which is easy to lose in the
finished matrix construction.  A calibrated native jet has two pieces of
data:

* its first column is the Green/Wronskian boundary response;
* its interior coefficients are transported by the one-step clock shift.

Together these are exactly the division-free polarized Green equation.  The
Hankel pair and the finite height operator are consequences of that equation
and of the already formalized injective incidence transport.  No matrix Gram,
Cholesky factor, Jacobi coordinate, or spectral fit is used to prove the
identity below.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open C3TraceDynamics

noncomputable section

/-! ## The algebraic seam before any Gram extraction -/

/--
The division-free coefficient equation is precisely the native boundary-plus-
shift law.  This is the identity which makes the Jacobi action inevitable:
the coefficient at (p,q+1) is the same coefficient at (p+1,q), while the
first column is the Green response.  The result is stated for an arbitrary
Hilbert-valued native jet, so it is not a reconstruction from a prescribed
Hankel matrix.
-/
theorem polarizedCoefficientVectorEquation_boundary_and_shift
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {rawJet : ℕ → E}
    (hcoeff : HasPolarizedCoefficientVectorEquation moments rawJet) :
    (∀ p : ℕ,
      inner ℂ (rawJet p) (rawJet 0) =
        oddMomentResponseCoefficient moments (p + 1)) ∧
      (∀ p q : ℕ,
        inner ℂ (rawJet p) (rawJet (q + 1)) =
          inner ℂ (rawJet (p + 1)) (rawJet q)) := by
  change IsPolarizedGreenCoefficientEquation moments
    (fun p q => inner ℂ (rawJet p) (rawJet q)) at hcoeff
  rcases
      (polarizedGreenCoefficientEquation_iff_boundary_transport moments
        (fun p q => inner ℂ (rawJet p) (rawJet q))).mp hcoeff with
    ⟨hboundary, hshift⟩
  exact ⟨hboundary, fun p q => (hshift p q).symm⟩

/-! ## C2 specialization: geometry supplies the shift law -/

/--
For the corrected native C2 atlas, the already formalized boundary
calibration and the exact seeded-clock reconstruction yield the two native
identities explicitly, before any Hankel/Jacobi construction.
-/
theorem canonicalC2Geometry_correctedNative_boundary_and_shift_before_gram
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block) :
    (∀ p : ℕ,
      inner ℂ (seededClockAtlasJet block p)
          (seededClockAtlasJet block 0) =
        oddMomentResponseCoefficient
          canonicalCompletedNativeLogDerivativeMoment (p + 1)) ∧
      (∀ p q : ℕ,
        inner ℂ (seededClockAtlasJet block p)
            (seededClockAtlasJet block (q + 1)) =
          inner ℂ (seededClockAtlasJet block (p + 1))
            (seededClockAtlasJet block q)) := by
  exact polarizedCoefficientVectorEquation_boundary_and_shift
    (canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
      M block htransport)

/-! ## The finite operator as the consequence of that native shift -/

/--
The source-direction capstone with the shift exposed in its conclusion.

The proof starts from the corrected C2 boundary transport, derives the
division-free two-variable Green equation, and only then invokes the native
incidence independence to obtain strict Stieltjes positivity and the finite
symmetric height operator.  Thus the operator is downstream of the native
Green/clock shift; the Hankel pair is not an input to the geometric identity.
-/
theorem canonicalC2Geometry_natural_source_to_height_operator_via_green_shift
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block))) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
    (∀ p : ℕ,
      inner ℂ (seededClockAtlasJet block p)
          (seededClockAtlasJet block 0) =
        oddMomentResponseCoefficient
          canonicalCompletedNativeLogDerivativeMoment (p + 1)) ∧
      (∀ p q : ℕ,
        inner ℂ (seededClockAtlasJet block p)
            (seededClockAtlasJet block (q + 1)) =
          inner ℂ (seededClockAtlasJet block (p + 1))
            (seededClockAtlasJet block q)) ∧
      ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
        normalizedCompletedNativeCameraCharacteristic 2 cutoff =
            (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
          completedNativeCameraLogDerivativeMoment 2 cutoff =
            canonicalCompletedNativeLogDerivativeMoment ∧
          (∃ hgram :
              (hankelGram
                (completedNativeCameraLogDerivativeMoment 2 cutoff) N).PosDef,
            canonicalFiniteJacobiSection
                (completedNativeCameraLogDerivativeMoment 2 cutoff) N hgram =
              canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
          (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  letI : InnerProductSpace ℝ
      (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
    InnerProductSpace.rclikeToReal ℂ _
  have hcoeff :
      HasPolarizedCoefficientVectorEquation
        canonicalCompletedNativeLogDerivativeMoment
        (seededClockAtlasJet block) :=
    canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
      M block htransport
  have hsplit := polarizedCoefficientVectorEquation_boundary_and_shift hcoeff
  have hchain :=
    canonicalC2Geometry_height_chain_of_coefficientEquation_and_incidenceTransport
      hbase hradius hcoeff transport cutoff N
  exact ⟨hsplit.1, hsplit.2, hchain⟩

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.NaturalNativeSourceValveGreenProvenance
import CarrySelfAdjointOperator.ProjectiveValveMomentFrontier
import CarrySelfAdjointOperator.GreenJetJacobiFiniteCompression
import CarrySelfAdjointOperator.CompletedNativeJacobiCyclicReadout
import CarrySelfAdjointOperator.BR2GreenFrameDslopeLimitBridge
import CarrySelfAdjointOperator.CompletedNativeChiralHankelDominance
import CarrySelfAdjointOperator.CompletedNativeRadialTiltSamplePositivity
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
open Filter

namespace CarrySelfAdjointOperator

open C3TraceDynamics
open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator
open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge

noncomputable section

/-! ## The Green Jacobi core forced by the coefficient equation -/

/-- The real Green representation extracted from the complex coefficient law. -/
theorem polarizedCoefficientVectorEquation_realMomentKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {rawJet : ℕ → E}
    (hcoeff : HasPolarizedCoefficientVectorEquation moments rawJet) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    IsGreenWronskianMomentKernelGramRepresentation moments
      (polarizedCoefficientParityJet rawJet) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hcomplex :=
    complexGreenWronskianMomentKernel_of_vectorCoefficientEquation hcoeff
  intro i j
  change greenWronskianMomentKernel moments i j =
    (inner ℂ
      (polarizedCoefficientParityJet rawJet i)
      (polarizedCoefficientParityJet rawJet j)).re
  have h := congrArg Complex.re (hcomplex i j)
  simpa using h

/--
The vector coefficient equation already supplies the real Green moment
representation needed by the algebraic Green Jacobi core.  Thus the core is
obtained from the native jet and its shift law, not introduced as an
independent matrix ansatz.
-/
theorem greenJacobiCore_formalSelfAdjoint_of_polarizedCoefficientVectorEquation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {rawJet : ℕ → E}
    (hcoeff : HasPolarizedCoefficientVectorEquation moments rawJet)
    (heven : LinearIndependent ℝ
      (fun n : ℕ =>
        polarizedCoefficientParityJet rawJet (Sum.inl n)))
    :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    ∀ x y :
      greenJetEvenOperatorCore (polarizedCoefficientParityJet rawJet),
      ⟪greenJetJacobiCoreMap heven x,
          (y : greenJetEvenHilbertSubspace
            (polarizedCoefficientParityJet rawJet))⟫_ℝ =
        ⟪(x : greenJetEvenHilbertSubspace
            (polarizedCoefficientParityJet rawJet)),
          greenJetJacobiCoreMap heven y⟫_ℝ := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  exact greenJetJacobiCore_formalSelfAdjoint
    (polarizedCoefficientVectorEquation_realMomentKernel hcoeff) heven

/-! ## C2 specialization of the Green Jacobi core -/

/--
The actual C2 incidence transport supplies the even independence required by
the Green core.  Hence the self-adjoint shift is obtained on the transported
native jet itself.
-/
theorem canonicalC2Geometry_greenJacobiCore_formalSelfAdjoint
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block))) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
    ∀ x y :
      greenJetEvenOperatorCore
        (polarizedCoefficientParityJet (seededClockAtlasJet block)),
      ⟪greenJetJacobiCoreMap
          (transport.even_linearIndependent hbase hradius) x,
          (y : greenJetEvenHilbertSubspace
            (polarizedCoefficientParityJet (seededClockAtlasJet block)))⟫_ℝ =
        ⟪(x : greenJetEvenHilbertSubspace
            (polarizedCoefficientParityJet (seededClockAtlasJet block))),
          greenJetJacobiCoreMap
            (transport.even_linearIndependent hbase hradius) y⟫_ℝ := by
  letI : InnerProductSpace ℝ
      (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
    InnerProductSpace.rclikeToReal ℂ _
  exact greenJacobiCore_formalSelfAdjoint_of_polarizedCoefficientVectorEquation
    (canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
      M block htransport)
    (transport.even_linearIndependent hbase hradius)

/--
At every finite order, the same C2 Green core has a Jacobi compression equal
to the canonical finite section.  This is the explicit operator-level
crosswalk; the inverse-square-root height operator is introduced only after
this shift compression and the strict odd-sector certificate.
-/
theorem canonicalC2Geometry_greenJacobiCore_finiteCompression
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M N : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block))) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
    (fun i j : Fin N =>
      ⟪greenJetJacobiCoreMap
          (transport.even_linearIndependent hbase hradius)
          (canonicalGreenJetEvenJacobiCoreVector
            (polarizedCoefficientVectorEquation_realMomentKernel
              (canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
                M block htransport))
            (transport.even_linearIndependent hbase hradius) N i),
        (canonicalGreenJetEvenJacobiCoreVector
            (polarizedCoefficientVectorEquation_realMomentKernel
              (canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
                M block htransport))
            (transport.even_linearIndependent hbase hradius) N j :
          greenJetEvenHilbertSubspace
            (polarizedCoefficientParityJet (seededClockAtlasJet block)))⟫_ℝ) =
      canonicalFiniteJacobiSection
        canonicalCompletedNativeLogDerivativeMoment N
        (canonicalGreenJetHankelGramCertificate
          (polarizedCoefficientVectorEquation_realMomentKernel
            (canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
              M block htransport))
          (transport.even_linearIndependent hbase hradius) N) := by
  letI : InnerProductSpace ℝ
      (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
    InnerProductSpace.rclikeToReal ℂ _
  exact greenJetJacobiCore_finiteCompression_eq_canonicalFiniteJacobiSection
    (polarizedCoefficientVectorEquation_realMomentKernel
      (canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
        M block htransport))
    (transport.even_linearIndependent hbase hradius) N

/-! ## The native scalar is the cyclic readout of the Green shift -/

/-- The Green Jacobi core realizes the native logarithmic moments on its cyclic
orbit.  This is the operator-level form of the script identity: the scalar
sequence is read from the shift generated by the native Hilbert jet, rather
than supplied as a spectral fit after the matrix has been built. -/
theorem canonicalC2Geometry_greenJacobiCore_cyclicMoment_eq_nativeMoment
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block)))
    (n : ℕ) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
    greenJetJacobiCoreCyclicMoment
        (transport.even_linearIndependent hbase hradius) n =
      canonicalCompletedNativeLogDerivativeMoment n := by
  letI : InnerProductSpace ℝ
      (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
    InnerProductSpace.rclikeToReal ℂ _
  exact greenJetJacobiCoreCyclicMoment_eq
    (polarizedCoefficientVectorEquation_realMomentKernel
      (canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
        M block htransport))
    (transport.even_linearIndependent hbase hradius) n

/-- The same cyclic readout is the corrected native chiral boundary
coefficient itself.  Thus the operator-level scalar is inherited directly
from the signed Green/TFVD readout, before the moment sequence is named. -/
theorem canonicalC2Geometry_greenJacobiCore_cyclicMoment_eq_correctedNativeChiralBoundary
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block)))
    (n : ℕ) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
    greenJetJacobiCoreCyclicMoment
        (transport.even_linearIndependent hbase hradius) n =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M (2 * n) := by
  letI : InnerProductSpace ℝ
      (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
    InnerProductSpace.rclikeToReal ℂ _
  calc
    (greenJetJacobiCoreCyclicMoment
          (transport.even_linearIndependent hbase hradius) n : ℂ) =
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
      exact_mod_cast
        (canonicalC2Geometry_greenJacobiCore_cyclicMoment_eq_nativeMoment
          hbase hradius M block htransport transport n)
    _ = canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M (2 * n) := by
      symm
      exact canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_odd_eq_canonicalMoment
        M n

/-- The cyclic moments of the Green Jacobi core are therefore the odd Taylor
coefficients of the completed native Wronskian response.  This is the direct
scalar provenance statement corresponding to the script's `closed_native_series`
readout; no matrix fit is used in this equality. -/
theorem canonicalC2Geometry_greenJacobiCore_cyclicMoment_eq_fullWronskianResponse
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block)))
    (n : ℕ) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
    greenJetJacobiCoreCyclicMoment
        (transport.even_linearIndependent hbase hradius) n =
      canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
        M (2 * n + 1) := by
  letI : InnerProductSpace ℝ
      (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
    InnerProductSpace.rclikeToReal ℂ _
  calc
    (greenJetJacobiCoreCyclicMoment
          (transport.even_linearIndependent hbase hradius) n : ℂ) =
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
      exact_mod_cast
        (canonicalC2Geometry_greenJacobiCore_cyclicMoment_eq_nativeMoment
          hbase hradius M block htransport transport n)
    _ = canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
          M (2 * n + 1) := by
      symm
      exact canonicalCompletedNativeCarryGreenChiralResponse_oddCoefficient_eq_moment
        M n

/-! The same cyclic readout is also the fully expanded native structural
signature.  This is the source-facing spelling of the operator readout:
the head, exact tail, completion, and chart-correction channels have already
been synthesized before the cyclic Green/Jacobi scalar is compared with the
moment sequence. -/
theorem canonicalC2Geometry_greenJacobiCore_cyclicMoment_eq_expandedStructuralSignature
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block)))
    (n : ℕ) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
    greenJetJacobiCoreCyclicMoment
        (transport.even_linearIndependent hbase hradius) n =
      canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
        M (2 * n + 1) := by
  letI : InnerProductSpace ℝ
      (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
    InnerProductSpace.rclikeToReal ℂ _
  calc
    (greenJetJacobiCoreCyclicMoment
          (transport.even_linearIndependent hbase hradius) n : ℂ) =
        canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
          M (2 * n + 1) := by
      exact_mod_cast
        (canonicalC2Geometry_greenJacobiCore_cyclicMoment_eq_fullWronskianResponse
          hbase hradius M block htransport transport n)
    _ = canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
          M (2 * n + 1) := by
      rw [canonicalCompletedC3ExpandedStructuralSignature_odd_eq_canonicalMoment,
        canonicalCompletedNativeCarryGreenChiralResponse_oddCoefficient_eq_moment]

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
  exact ⟨hboundary, hshift⟩

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

/-! ## One-piece source-direction capstone -/

/--
The C2/valve/Green genealogy and the corrected native shift can be consumed
in one source-direction theorem.  The first conjunct is the exact pre-Gram
record: dyadic C2 incidence, bracket readout, exact centre-tail sewing,
completion, valve identities, causal Green return, and the four-corner
carrier.  The second conjunct is the shift capstone above, which turns the
corrected Green boundary transport and the already formalized injective
incidence transport into the finite symmetric height operator.

This theorem is intentionally a conjunction of existing native identities,
not a new operator-to-geometry reconstruction.  In particular, the
corrected boundary transport remains visible as an input rather than being
silently replaced by a positive Gram proxy.
-/
theorem canonicalC2Geometry_native_source_valve_green_to_height_via_correctedShift
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block))) :
    (∀ (tailCutoff : ℕ) {s : ℂ}, s ∈ nativeScalarDomain →
        finiteBracketCharacteristic 2 tailCutoff s +
            (∑' index : ℕ,
              centerBracketTerm 2 s (index + tailCutoff)) =
          factor 2 s * nativeScalar s) ∧
      (∀ (packagedCutoff : ℕ) (time : ℝ),
        nativeXiCompletionFactor (time : ℂ) *
            completedPackagedFiniteNativeOperatorJet
              2 packagedCutoff 0 time /
              factor 2 (nativeLine time) =
          completedNativeOperatorCharacteristic (time : ℂ)) ∧
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
  rcases canonicalC2Geometry_native_source_valve_green_preGram hbase hradius with
    ⟨hsource, hfinite, hallorder, htail, hpackaged, heven, hcurvature,
      hderiv, hcausal, hfourcorner, hsewing⟩
  have hchain :=
    canonicalC2Geometry_natural_source_to_height_operator_via_green_shift
      hbase hradius M cutoff N block htransport transport
  exact ⟨htail, hpackaged, hchain.2.2⟩

/-! ## The stronger native Green identity route -/

/-- A division-free native Green/Wronskian identity, together with continuity
of the actual Hilbert state, already supplies the real-axis normalized kernel
used by the completed forward-difference construction.  This is the natural
route from the Green identity to the jet; no Gram, Hankel, Jacobi, or fitted
finite atlas is used in the proof. -/
theorem hasCanonicalCompletedNativeRealAxisNormalizedGreenKernel_of_divisionFreeGreen
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {state : ℂ → E}
    (hgreen : HasDivisionFreeGreenRepresentation
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    (hstate : Continuous state) :
    HasCompletedNativeRealAxisNormalizedGreenKernel state := by
  intro x z hxF hzF
  have hgreenOn :
      HasDivisionFreeGreenRepresentationOn
        completedNativeHeightDomain
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion state := by
    intro u hu v hv
    exact hgreen u v
  have hxDomain : completedNativeHeightDomain ∈ nhds (x : ℂ) :=
    isOpen_completedNativeHeightDomain.mem_nhds
      (ofReal_mem_completedNativeHeightDomain x)
  have hxAnalytic := completedNativeOperatorCharacteristic_analyticAt
    (ofReal_mem_completedNativeHeightDomain x)
  have hxFEvent : ∀ᶠ u in nhds (x : ℂ),
      completedNativeOperatorCharacteristic u ≠ 0 :=
    hxAnalytic.continuousAt.eventually_ne hxF
  have hresponse : DifferentiableAt ℂ
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) (x : ℂ) := by
    rw [show completedNativeOperatorBoundaryCompanion =
        fun u => -deriv completedNativeOperatorCharacteristic u by
      funext u
      exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u]
    unfold completedGreenNormalizedResponse
    exact (hxAnalytic.deriv.neg.div
      (analyticAt_const.mul hxAnalytic)
      (mul_ne_zero (by norm_num) hxF)).differentiableAt
  apply normalizedCompletedGreenState_inner_eq_dslope hgreenOn hxDomain hxFEvent
  · simp
  · exact completedNativeGreenNormalizedResponse_ofReal_conj x
  · exact continuousAt_normalizedCompletedGreenState
      hxAnalytic.continuousAt hxF hstate.continuousAt
  · exact hresponse
  · exact ofReal_mem_completedNativeHeightDomain z
  · exact hzF

/-- Source-direction capstone for the strong Green identity.  The order is
explicit: division-free native Green representation, real-axis normalized
kernel, completed Green jet, and only then the already-proved injective native
incidence transport.  The finite symmetric height operator is consequently
downstream of the native identity rather than its definition. -/
theorem canonicalC2Geometry_height_chain_of_divisionFreeGreen_and_incidenceTransport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (state : ℂ → E)
    (hgreen : HasDivisionFreeGreenRepresentation
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    (hstate : Continuous state)
    (transport : BR2BracketIncidenceJetTransport base radius
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state
        (hasCanonicalCompletedNativeRealAxisNormalizedGreenKernel_of_divisionFreeGreen
          hgreen hstate)))
    (cutoff N : ℕ) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      normalizedCompletedNativeCameraCharacteristic 3 cutoff =
          (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
        completedNativeCameraLogDerivativeMoment 3 cutoff =
          canonicalCompletedNativeLogDerivativeMoment ∧
        (∃ hgram :
            (hankelGram
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N).PosDef,
          canonicalFiniteJacobiSection
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N hgram =
            canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
        (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state :=
    hasCanonicalCompletedNativeRealAxisNormalizedGreenKernel_of_divisionFreeGreen
      hgreen hstate
  have hmoment :=
    canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
      state hkernel
  exact nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport
    hbase hradius hmoment transport cutoff N

/-! ## The vector-defect form of the same source route -/

/-- The incidence transport need not be postulated separately.  The already
formalized Green-frame bridge constructs it from the vanishing of the full
analyzed vector defect against the BR2 jet.  This is the native source-facing
form of the capstone: the only non-algebraic inputs are the division-free
Green identity, continuity of the selected state, and the actual vector
convergence of the Green-frame approximants. -/
theorem canonicalC2Geometry_height_chain_of_divisionFreeGreen_and_greenFrameDefect
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (state : ℂ → CarryVerticalL2)
    (hgreen : HasDivisionFreeGreenRepresentation
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    (hstate : Continuous state)
    (hdefect : ∀ i : ℕ ⊕ ℕ,
      Tendsto
        (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
            (completedGreenForwardDifferenceParityJet
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state) k i) -
          br2CameraBracketGreenFrameParityJet base radius i)
        atTop (nhds 0))
    (cutoff N : ℕ) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      normalizedCompletedNativeCameraCharacteristic 3 cutoff =
          (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
        completedNativeCameraLogDerivativeMoment 3 cutoff =
          canonicalCompletedNativeLogDerivativeMoment ∧
        (∃ hgram :
            (hankelGram
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N).PosDef,
          canonicalFiniteJacobiSection
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N hgram =
            canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
        (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  let hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state :=
    hasCanonicalCompletedNativeRealAxisNormalizedGreenKernel_of_divisionFreeGreen
      hgreen hstate
  let htransport :=
    canonicalCompletedNativeRealTfvdGreenMomentTransport_of_greenFrameDefect
      state hkernel hdefect
  have hinc : BR2BracketIncidenceJetTransport base radius
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state hkernel) := by
    simpa [htransport,
      canonicalCompletedNativeRealTfvdGreenMomentTransport_of_greenFrameDefect,
      canonicalCompletedNativeRealTfvdGreenMomentTransport_of_vectorLimit_eq_projective,
      canonicalCompletedNativeRealTfvdGreenMomentTransport_of_vectorLimit,
      canonicalCompletedNativeGreenForwardDifferenceLimitParityJet] using
      htransport.incidenceTransport
  exact canonicalC2Geometry_height_chain_of_divisionFreeGreen_and_incidenceTransport
    hbase hradius state hgreen hstate hinc cutoff N

/-! ## The expanded structural signature forces the same operator -/

/-- The completed structural signature is already the source-side scalar from
the native Green construction: its odd Taylor coefficients are the canonical
logarithmic moments, and its two regularized Loewner blocks are therefore the
unshifted and shifted Hankel towers.  Once the genuinely geometric chiral
dominance gate is supplied, the finite height operator follows without a
material-clock first-column calibration.  This is the direct structural
route; the separate clock transport remains available when one wants the
literal seeded-clock carrier.
-/
theorem canonicalC2Geometry_natural_source_to_height_operator_of_expandedStructuralDominance
    (hdominance : CanonicalCompletedC3ExpandedStructuralStrictChiralDominance)
    (cutoff N : ℕ) :
    canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect 0 N =
        hankelGram canonicalCompletedNativeLogDerivativeMoment N ∧
      canonicalCompletedC3ExpandedStructuralOddLoewnerDefect 0 N =
        shiftedHankel canonicalCompletedNativeLogDerivativeMoment N ∧
      ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
        normalizedCompletedNativeCameraCharacteristic 3 cutoff =
            (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
          completedNativeCameraLogDerivativeMoment 3 cutoff =
            canonicalCompletedNativeLogDerivativeMoment ∧
          (∃ hgram :
              (hankelGram
                (completedNativeCameraLogDerivativeMoment 3 cutoff) N).PosDef,
            canonicalFiniteJacobiSection
                (completedNativeCameraLogDerivativeMoment 3 cutoff) N hgram =
              canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
          (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  have heven :=
    canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect_eq_hankel 0 N
  have hodd :=
    canonicalCompletedC3ExpandedStructuralOddLoewnerDefect_eq_shiftedHankel 0 N
  have hpos : CanonicalCompletedNativeStieltjesPositivity :=
    (canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity).mp
      hdominance
  exact ⟨heven, hodd,
    ⟨hpos, nativeGeometry_to_finiteHeight_chain (camera := 3) (by norm_num)
      cutoff N hpos⟩⟩

/-- The preceding structural capstone can be fed directly by the native
radial Green/valve gates.  The ledger no-leak identity supplies the limiting
chiral form, while the uniform determinant lower bound prevents collapse of
the parity sectors.  Hence the self-adjoint height section is downstream of
the native radial geometry even when the literal seeded-clock first column is
not yet transported.
-/
theorem canonicalC2Geometry_natural_source_to_height_operator_of_radialLedger
    (hnoLeak : CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound)
    (cutoff N : ℕ) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      normalizedCompletedNativeCameraCharacteristic 3 cutoff =
          (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
        completedNativeCameraLogDerivativeMoment 3 cutoff =
          canonicalCompletedNativeLogDerivativeMoment ∧
        (∃ hgram :
            (hankelGram
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N).PosDef,
          canonicalFiniteJacobiSection
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N hgram =
            canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
        (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  have hpos : CanonicalCompletedNativeStieltjesPositivity :=
    canonicalCompletedNativeStieltjesPositivity_of_radialLedger hnoLeak hstrict
  have hdominance : CanonicalCompletedC3ExpandedStructuralStrictChiralDominance :=
    (canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity).mpr
      hpos
  exact
    (canonicalC2Geometry_natural_source_to_height_operator_of_expandedStructuralDominance
      hdominance cutoff N).2.2

end

end CarrySelfAdjointOperator

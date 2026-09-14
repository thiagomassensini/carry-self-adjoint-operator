import CarrySelfAdjointOperator.CompletedNativeCorrectedClockBoundaryGate
import CarrySelfAdjointOperator.CompletedNativeClockGreenMomentGate
import CarrySelfAdjointOperator.C2GeometryNativeSourceBridge
import CarrySelfAdjointOperator.BR2IncidenceStrictPositivity
import CarrySelfAdjointOperator.CompletedNativeHPGateAudit
import CarrySelfAdjointOperator.CompletedNativeGeometryHeightProvenance
import CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesOperator
import Mathlib.Tactic

/-!
# Corrected native geometry to finite height provenance

This is the source-direction composition of the already proved gates.  The
corrected causal/chiral readout is formed before Hankel or Jacobi.  A material
clock is admitted only through the explicit first-column transport to that
readout.  The existing clock shift then supplies the two-variable Green
kernel; parity independence supplies strictness; only after those steps is the
canonical finite height operator introduced.

No camera Gram, Cholesky factor, Jacobi matrix, or fitted normalization is used
as an input to the native identity.  The theorem is deliberately conditional
on the remaining material calibration and parity certificates.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics
open FiniteNativeCarryOperator.Camera
open CPFormal.Carry.C2
open CPFormal.Carry.Cp
open CPFormal.Carry.Positional
open ProjectiveDepth
open FiniteNativeCarryOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge

noncomputable section

/-! ## The complete source-direction finite chain -/

theorem canonicalC2Geometry_correctedNative_to_finiteHeight_chain
    {ι : Type*} [Fintype ι]
    (M cutoff N : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (heven : LinearIndependent ℂ
      (fun n : ℕ => seededClockAtlasJet block (2 * n)))
    (hodd : LinearIndependent ℂ
      (fun n : ℕ => seededClockAtlasJet block (2 * n + 1))) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
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
  have hcertificate :
      CompletedNativeRealHPCarrierCertificate
        (polarizedCoefficientParityJet (seededClockAtlasJet block)) := by
    exact completedNativeRealHPCarrierCertificate_of_correctedNativeChiralBoundaryTransport
      M block htransport heven hodd
  let hpos : CanonicalCompletedNativeStieltjesPositivity :=
    canonicalCompletedNativeStieltjesPositivity_of_certificate hcertificate
  refine ⟨hpos, ?_⟩
  exact ⟨
    nativeGeometry_normalizedCamera_eq_commonCharacteristic (camera := 2)
      (by norm_num) cutoff,
    nativeGeometry_cameraMoments_eq_canonical (camera := 2)
      (by norm_num) cutoff,
    nativeGeometry_cameraJacobiSection_eq_canonical (camera := 2)
      (by norm_num) cutoff N hpos,
    nativeGeometryFiniteHeightOperator_isSymm hpos N⟩

/-! ## The pre-Hankel part of the same composition -/

theorem canonicalC2Geometry_correctedNative_greenKernel_before_height
    {ι : Type*} [Fintype ι]
    (M cutoff : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block) :
    IsComplexGreenWronskianMomentKernelGramRepresentation
      (completedNativeCameraLogDerivativeMoment 2 cutoff)
      (polarizedCoefficientParityJet (seededClockAtlasJet block)) := by
  exact canonicalC2Geometry_seededClockGreenMomentKernel_of_correctedTransport
    M cutoff block htransport

/-! The same statement with the canonical scalar readout exposed. -/

theorem canonicalC2Geometry_correctedNative_greenKernel_eq_canonical
    {ι : Type*} [Fintype ι]
    (M cutoff : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block) :
    IsComplexGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment
      (polarizedCoefficientParityJet (seededClockAtlasJet block)) := by
  rw [← canonicalC2Geometry_cameraMoments_eq_canonical cutoff]
  exact canonicalC2Geometry_correctedNative_greenKernel_before_height
    M cutoff block htransport

/-! ## The pre-Gram coefficient equation -/

/-- The corrected native calibration and the material-clock shift already give
the complete polarized coefficient equation before any Gram/Hankel object is
introduced.  The proof uses only the exact first-column ledger identity and
the interior shift of the reconstructed C3 clock. -/
theorem canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block) :
    HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      (seededClockAtlasJet block) := by
  have hboundary : ∀ p : ℕ,
      seededClockAtlasCoefficient block p 0 =
        canonicalCompletedC3LedgerBoundaryTaylorCoefficient M p := by
    intro p
    exact canonicalCompletedC3LedgerBoundary_of_correctedNativeChiralBoundaryTransport
      M block htransport p
  have hscalar :
      IsPolarizedGreenCoefficientEquation
        canonicalCompletedNativeLogDerivativeMoment
        (seededClockAtlasCoefficient block) :=
    seededClockAtlasCoefficient_equation_of_completedLedgerBoundary
      M block hboundary
  change IsPolarizedGreenCoefficientEquation
    canonicalCompletedNativeLogDerivativeMoment
    (fun p q => inner ℂ (seededClockAtlasJet block p)
      (seededClockAtlasJet block q))
  rw [show (fun p q => inner ℂ (seededClockAtlasJet block p)
      (seededClockAtlasJet block q)) = seededClockAtlasCoefficient block by
    funext p q
    exact (seededClockAtlasCoefficient_eq_inner block p q).symm]
  exact hscalar

/-! ## Coefficient equation plus native incidence transport -/

/-- The non-vacuous source-direction interface: a native coefficient equation
is combined with the already formalized injective incidence transport.  The
transport supplies strict parity independence in the actual completed
carrier; no finite atomic atlas is used as an all-order Hilbert space. -/
theorem canonicalC2Geometry_height_chain_of_coefficientEquation_and_incidenceTransport
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    {rawJet : ℕ → E}
    (hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment rawJet)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet rawJet))
    (cutoff N : ℕ) :
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
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hcomplex :=
    complexGreenWronskianMomentKernel_of_vectorCoefficientEquation hcoeff
  have hcertificate :
      CompletedNativeRealHPCarrierCertificate
        (polarizedCoefficientParityJet rawJet) :=
    { momentKernel := by
        intro i j
        change greenWronskianMomentKernel
            canonicalCompletedNativeLogDerivativeMoment i j =
          (inner ℂ (polarizedCoefficientParityJet rawJet i)
            (polarizedCoefficientParityJet rawJet j)).re
        have h := congrArg Complex.re (hcomplex i j)
        simpa using h
      evenIndependent := transport.even_linearIndependent hbase hradius
      oddIndependent := transport.odd_linearIndependent hbase hradius }
  let hpos : CanonicalCompletedNativeStieltjesPositivity :=
    canonicalCompletedNativeStieltjesPositivity_of_certificate hcertificate
  refine ⟨hpos, ?_⟩
  exact ⟨
    nativeGeometry_normalizedCamera_eq_commonCharacteristic (camera := 2)
      (by norm_num) cutoff,
    nativeGeometry_cameraMoments_eq_canonical (camera := 2)
      (by norm_num) cutoff,
    nativeGeometry_cameraJacobiSection_eq_canonical (camera := 2)
      (by norm_num) cutoff N hpos,
    nativeGeometryFiniteHeightOperator_isSymm hpos N⟩

/-! ## One-piece natural source-to-operator capstone -/

/-- The complete source-direction genealogy of the finite height operator.

The first four conjuncts are the native geometric/readout identities: the C2
cell is written in its dyadic fibre coordinates, the finite camera is the
seed plus its fibre brackets, the omitted centre tail is sewn exactly, and
the completed zero-order readout is factor-cancelled to the common native
characteristic.  Only then is the corrected boundary transport converted
into the polarized coefficient equation.  The final conjunct consumes that
equation together with the already formalized parity independence and
produces the Stieltjes positivity certificate, the finite Jacobi section,
and the symmetric height operator.

Thus this theorem records the natural direction
`native geometry -> Green/readout -> coefficient equation -> positivity ->
height operator`; no Gram, Cholesky, Jacobi, or fitted spectral datum is used
to prove any of the source identities.  The sole material input remains the
named corrected-native boundary transport. -/
theorem canonicalC2Geometry_natural_source_to_height_operator
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (M cutoff N : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block))) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
    (∀ j : ℕ,
        4 * (j + 1) =
            2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j ∧
          ((leftIncidence j).1.2 : ℝ) =
            c2FiberPoint (c2AlignedIndexCore j) (-1)
              (c2AlignedIndexDepth j) ∧
          ((rightIncidence j).1.2 : ℝ) =
            c2FiberPoint (c2AlignedIndexCore j) 1
              (c2AlignedIndexDepth j) ∧
          CPFormal.Carry.C2.effectiveDepth (leftIncidence j).1.2 =
            c2AlignedIndexDepth j ∧
          CPFormal.Carry.C2.effectiveDepth (rightIncidence j).1.2 =
            c2AlignedIndexDepth j ∧
          Real.log ((4 * (j + 1) : ℕ) : ℝ) =
            (c2AlignedIndexDepth j : ℝ) * Real.log 2 +
              primeDepthLogLedger (c2AlignedIndexCore j) ∧
          Real.log ((4 * (j + 1) : ℕ) : ℝ) *
              CPFormal.Carry.Cp.criticalAmplitude 2
                (c2AlignedIndexDepth j) =
            Real.log 2 * ProjectiveDepth.newtonJet
                (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 1
                  (c2AlignedIndexDepth j) +
              primeDepthLogLedger (c2AlignedIndexCore j) *
                ProjectiveDepth.newtonJet
                  (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 0
                    (c2AlignedIndexDepth j)) ∧
      (∀ order : ℕ,
        evalFormalStencil
            (fun n => nativeDirichletSlopeTaylorCoefficient order n)
            (finiteStencil 2 M) =
          evalFormalStencil
              (fun n => nativeDirichletSlopeTaylorCoefficient order n)
              (seedStencil 2) +
            ∑ j ∈ Finset.range M,
              c2FiberNativeTaylorBracket order
                (c2AlignedIndexCore j) (c2AlignedIndexDepth j)) ∧
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
      HasPolarizedCoefficientVectorEquation
        canonicalCompletedNativeLogDerivativeMoment
        (seededClockAtlasJet block) ∧
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
  have hcoeff :=
    canonicalC2Geometry_correctedNative_coefficientEquation_before_gram
      M block htransport
  have hchain :=
    canonicalC2Geometry_height_chain_of_coefficientEquation_and_incidenceTransport
      hbase hradius hcoeff transport cutoff N
  rcases hchain with ⟨hpos, hnorm, hmom, hjac, hsym⟩
  refine ⟨?_, ?_, ?_, ?_, hcoeff, ⟨hpos, hnorm, hmom, hjac, hsym⟩⟩
  · intro j
    exact canonicalC2Geometry_nativeSourceChain j
  · intro order
    exact canonicalC2Geometry_nativeTaylorReadout_eq_seed_add_fibreBrackets
      M order
  · intro tailCutoff s hs
    exact canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar
      tailCutoff hs
  · intro packagedCutoff time
    exact canonicalC2Geometry_completedPackagedNativeJet_zero_normalized_eq_commonCharacteristic
      packagedCutoff time



/-! ## The native center--leg certificate to height -/

/-- A genuine center--leg Green certificate is the direct source-direction
seam into the finite height construction.  Its scalar readout is converted to
the real Green moment kernel, while the already formalized injective incidence
transport supplies strict parity independence.  The C2 camera identities are
used only after this native carrier has produced the positivity certificate.
-/
theorem canonicalC2Geometry_height_chain_of_centerLegGreenCertificate
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (incidence : BR2CameraIncidence)
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (certificate :
      BR2CenterLegGreenMomentCertificate incidence moments jet)
    (transport :
      BR2BracketIncidenceJetTransport
        incidence.base incidence.radius jet)
    (hmoments :
      moments = canonicalCompletedNativeLogDerivativeMoment)
    (cutoff N : ℕ) :
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
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hgreen :
      IsGreenWronskianMomentKernelGramRepresentation
        canonicalCompletedNativeLogDerivativeMoment jet := by
    rw [← hmoments]
    exact certificate.toRealMomentKernel
  have hchain :=
    nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport
      incidence.hbase incidence.hradius hgreen transport cutoff N
  rcases hchain with ⟨hpos, _, _, _, _⟩
  exact ⟨hpos,
    nativeGeometry_normalizedCamera_eq_commonCharacteristic (camera := 2)
      (by norm_num) cutoff,
    nativeGeometry_cameraMoments_eq_canonical (camera := 2)
      (by norm_num) cutoff,
    nativeGeometry_cameraJacobiSection_eq_canonical (camera := 2)
      (by norm_num) cutoff N hpos,
    nativeGeometryFiniteHeightOperator_isSymm hpos N⟩

/-! ## The stronger pre-Gram state/readout seam -/

/-- The direct TFVD/Green route: a pointwise center--leg readout identity is
enough to produce the carrier certificate and hence the finite height
operator.  This is the exact geometric input before any Hankel or Jacobi
object is formed. -/
theorem canonicalC2Geometry_height_chain_of_tfvdGreenCenterLegReadout
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    {jet : (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier}
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (incidence : BR2CameraIncidence)
    (hreadout : HasCanonicalCompletedNativeTfvdGreenCenterLegReadout
      incidence jet)
    (cutoff N : ℕ) :
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
  letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
    InnerProductSpace.rclikeToReal ℂ _
  have hcertificate : CompletedNativeRealHPCarrierCertificate jet :=
    completedNativeRealHPCarrierCertificate_of_centerLegReadout
      hbase hradius transport incidence hreadout
  let hpos : CanonicalCompletedNativeStieltjesPositivity :=
    canonicalCompletedNativeStieltjesPositivity_of_certificate hcertificate
  exact ⟨hpos,
    nativeGeometry_normalizedCamera_eq_commonCharacteristic (camera := 2)
      (by norm_num) cutoff,
    nativeGeometry_cameraMoments_eq_canonical (camera := 2)
      (by norm_num) cutoff,
    nativeGeometry_cameraJacobiSection_eq_canonical (camera := 2)
      (by norm_num) cutoff N hpos,
    nativeGeometryFiniteHeightOperator_isSymm hpos N⟩

end

end CarrySelfAdjointOperator

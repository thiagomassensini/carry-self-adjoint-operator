import CarrySelfAdjointOperator.CompletedNativeCorrectedClockBoundaryGate
import CarrySelfAdjointOperator.C2GeometryNativeSourceBridge
import CarrySelfAdjointOperator.BR2IncidenceStrictPositivity
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

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedC3CompressedSourceTailControl

/-!
# Closed compressed C3 resolvent realization

The finite completed TFVD states and their compressed logarithmic images
converge strongly.  Formal symmetry on the dense compressed domain makes the
compressed logarithmic operator closable, so the two strong limits form a
point in the graph of its canonical closure.  Passing the exact finite defect
equation to the limit then produces the intrinsic compressed resolvent
equation with the completed Hilbert source.

This construction stays entirely on the compressed camera carrier.  It does
not require disappearance of the complementary Naimark channel.
-/

open scoped ComplexConjugate InnerProductSpace LinearPMap lp

namespace CarrySelfAdjointOperator

open Filter
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The densely defined formally symmetric compressed logarithmic operator is
closable. -/
theorem realifiedCompressedLogarithmicMultiplication_isClosable :
    realifiedCompressedLogarithmicMultiplication.IsClosable := by
  exact linearPMap_isClosable_of_dense_formalAdjoint
    realifiedCompressedLogarithmicMultiplication
    realifiedCompressedLogarithmicMultiplication
    realifiedCompressedLogarithmicMultiplication_denseDomain
    realifiedCompressedLogarithmicMultiplication_isFormalAdjoint

/-- The completed TFVD camera state and the intrinsic compressed logarithmic
image form a point in the graph of the canonical closed realization. -/
theorem completedC3CompressedLogarithmicLimit_mem_closure_graph
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    (completedC3SymplecticCameraState (operatorHeightParameter z) hs,
        completedC3CompressedLogarithmicImageLimit
          (operatorHeightParameter z)) ∈
      realifiedCompressedLogarithmicMultiplication.closure.graph := by
  let state (cutoff : Nat) :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
      hbase cutoff z
  have hstate : Tendsto
      (fun cutoff : Nat => (state cutoff : RealifiedCameraComplexification))
      atTop
      (nhds (completedC3SymplecticCameraState
        (operatorHeightParameter z) hs)) := by
    simpa only [state] using
      canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
        hbase z hs
  have himage : Tendsto
      (fun cutoff : Nat =>
        realifiedCompressedLogarithmicMultiplication (state cutoff))
      atTop
      (nhds (completedC3CompressedLogarithmicImageLimit
        (operatorHeightParameter z))) := by
    simpa only [state] using
      canonicalCompletedC3FiniteCompressedLogarithmicImage_tendsto hbase z hs
  have hpair : Tendsto
      (fun cutoff : Nat =>
        ((state cutoff : RealifiedCameraComplexification),
          realifiedCompressedLogarithmicMultiplication (state cutoff)))
      atTop
      (nhds
        (completedC3SymplecticCameraState (operatorHeightParameter z) hs,
          completedC3CompressedLogarithmicImageLimit
            (operatorHeightParameter z))) :=
    hstate.prodMk_nhds himage
  rw [←
    realifiedCompressedLogarithmicMultiplication_isClosable.graph_closure_eq_closure_graph]
  exact realifiedCompressedLogarithmicMultiplication.graph.isClosed_topologicalClosure.mem_of_tendsto
    hpair
    (Eventually.of_forall fun cutoff =>
      realifiedCompressedLogarithmicMultiplication.graph.le_topologicalClosure
        (realifiedCompressedLogarithmicMultiplication.mem_graph (state cutoff)))

/-- The graph-limit vector in the closed compressed domain, with its action
identified by the all-camera logarithmic series. -/
theorem exists_completedC3CompressedLogarithmicClosureCandidate
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    ∃ candidate : realifiedCompressedLogarithmicMultiplication.closure.domain,
      (candidate : RealifiedCameraComplexification) =
          completedC3SymplecticCameraState (operatorHeightParameter z) hs ∧
        realifiedCompressedLogarithmicMultiplication.closure candidate =
          completedC3CompressedLogarithmicImageLimit
            (operatorHeightParameter z) := by
  have hgraph :=
    completedC3CompressedLogarithmicLimit_mem_closure_graph hbase z hs
  rw [LinearPMap.mem_graph_iff] at hgraph
  exact hgraph

/-- The completed compressed source is exactly the defect between the scalar
part and the logarithmic image. -/
theorem canonicalCompletedC3CompressedHilbertSource_eq_scalar_sub_image
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs)
    (hsource : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource z hs hbound))) :
    canonicalCompletedC3CompressedHilbertSource z hs hbound =
      realifiedCompressedScalar z
          (completedC3SymplecticCameraState (operatorHeightParameter z) hs) -
        completedC3CompressedLogarithmicImageLimit
          (operatorHeightParameter z) := by
  have hstate :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
      hbase z hs
  have hscalar : Tendsto
      (fun cutoff : Nat =>
        realifiedCompressedScalar z
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z : RealifiedCameraComplexification))
      atTop
      (nhds (realifiedCompressedScalar z
        (completedC3SymplecticCameraState (operatorHeightParameter z) hs))) :=
    (realifiedCompressedScalar z).continuous.continuousAt.tendsto.comp hstate
  have himage :=
    canonicalCompletedC3FiniteCompressedLogarithmicImage_tendsto hbase z hs
  have hdefect := (hscalar.sub himage).congr'
    (Eventually.of_forall fun cutoff => by
      exact
        canonicalCompletedC3CausalResponseBoundaryFinite_scalar_sub_compressedLogarithmic_eq_source
          hbase cutoff z)
  exact tendsto_nhds_unique hsource hdefect

/-- Canonical closed compressed resolvent realization.  The source is the
strong Hilbert limit of the finite compressed defects, and the response lies
in the domain of the graph closure of the compressed logarithmic operator. -/
theorem exists_canonicalCompletedC3CompressedResolventCandidate
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    ∃ hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs,
      ∃ candidate : realifiedCompressedLogarithmicMultiplication.closure.domain,
        (candidate : RealifiedCameraComplexification) =
            completedC3SymplecticCameraState (operatorHeightParameter z) hs ∧
          realifiedCompressedScalar z
              (candidate : RealifiedCameraComplexification) =
            realifiedCompressedLogarithmicMultiplication.closure candidate +
              canonicalCompletedC3CompressedHilbertSource z hs hbound := by
  rcases exists_canonicalCompletedC3CompressedHilbertSource_tendsto
      hbase z hs with ⟨hbound, hsource⟩
  rcases exists_completedC3CompressedLogarithmicClosureCandidate
      hbase z hs with ⟨candidate, hcandidate, himage⟩
  refine ⟨hbound, candidate, hcandidate, ?_⟩
  rw [himage,
    canonicalCompletedC3CompressedHilbertSource_eq_scalar_sub_image
      hbase z hs hbound hsource,
    hcandidate]
  abel

end

end CarrySelfAdjointOperator

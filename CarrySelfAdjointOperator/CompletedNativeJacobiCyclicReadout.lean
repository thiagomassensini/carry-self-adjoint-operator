import CarrySelfAdjointOperator.CompletedNativeGreenWeylHeight
import Mathlib.Tactic

/-!
# Completed native cyclic Jacobi readout

The Green-jet Jacobi core acts by `J e_n = e_(n+1)`.  This file retains that
action as an endomorphism of the algebraic core and identifies its cyclic
moments with the logarithmic moments of the completed native characteristic.

It also proves the exact truncated resolvent identity

`(I - u J) (sum_{k=0}^N u^k e_k) = e_0 - u^(N+1) e_(N+1)`.

The final term is kept explicit; no convergence or boundedness assertion is
inserted into the finite identity.
-/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- The Jacobi shift retained as an endomorphism of its algebraic Green core. -/
def greenJetJacobiCoreEndomorphism
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    Module.End ℝ (greenJetEvenOperatorCore jet) :=
  (greenJetEvenOperatorCoreBasis heven).constr ℝ
    (fun n => greenJetEvenCoreJet jet (n + 1))

@[simp] theorem greenJetJacobiCoreEndomorphism_jet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    greenJetJacobiCoreEndomorphism heven (greenJetEvenCoreJet jet n) =
      greenJetEvenCoreJet jet (n + 1) := by
  rw [← greenJetEvenOperatorCoreBasis_apply heven n]
  exact (greenJetEvenOperatorCoreBasis heven).constr_basis ℝ
    (fun n => greenJetEvenCoreJet jet (n + 1)) n

/-- The retained core endomorphism is the already constructed Jacobi
`LinearPMap` action after inclusion into the even Hilbert sector. -/
theorem greenJetJacobiCoreEndomorphism_coe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (x : greenJetEvenOperatorCore jet) :
    ((greenJetJacobiCoreEndomorphism heven x :
        greenJetEvenOperatorCore jet) : greenJetEvenHilbertSubspace jet) =
      greenJetJacobiCoreMap heven x := by
  let inclusion : greenJetEvenOperatorCore jet →ₗ[ℝ]
      greenJetEvenHilbertSubspace jet :=
    (greenJetEvenOperatorCore jet).subtype
  have hmaps :
      inclusion.comp (greenJetJacobiCoreEndomorphism heven) =
        greenJetJacobiCoreMap heven := by
    apply (greenJetEvenOperatorCoreBasis heven).ext
    intro n
    rw [greenJetEvenOperatorCoreBasis_apply,
      LinearMap.comp_apply, greenJetJacobiCoreEndomorphism_jet,
      greenJetJacobiCoreMap_jet]
    rfl
  exact LinearMap.congr_fun hmaps x

/-- The `n`-fold Jacobi shift sends the head vector exactly to `e_n`. -/
@[simp] theorem greenJetJacobiCoreEndomorphism_pow_head
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    (greenJetJacobiCoreEndomorphism heven ^ n)
        (greenJetEvenCoreJet jet 0) =
      greenJetEvenCoreJet jet n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih,
        greenJetJacobiCoreEndomorphism_jet]

/-- Scalar cyclic moment of the actual algebraic Jacobi action. -/
def greenJetJacobiCoreCyclicMoment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) : ℝ :=
  ⟪(((greenJetJacobiCoreEndomorphism heven ^ n)
      (greenJetEvenCoreJet jet 0) : greenJetEvenOperatorCore jet) :
        greenJetEvenHilbertSubspace jet),
    greenJetEvenSectorJet jet 0⟫_ℝ

/-- The cyclic Jacobi moments are exactly the moments of the Green Gram
kernel. -/
theorem greenJetJacobiCoreCyclicMoment_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    greenJetJacobiCoreCyclicMoment heven n = moments n := by
  unfold greenJetJacobiCoreCyclicMoment
  rw [greenJetJacobiCoreEndomorphism_pow_head]
  change ⟪greenJetEvenSectorJet jet n,
    greenJetEvenSectorJet jet 0⟫_ℝ = moments n
  simpa using inner_greenJetEvenSectorJet_eq_moment hrep n 0

/-- Finite geometric resolvent vector on the Jacobi core. -/
def greenJetJacobiCoreResolventPrefix
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (u : ℝ) (N : ℕ) : greenJetEvenOperatorCore jet :=
  ∑ k ∈ Finset.range (N + 1),
    u ^ k • greenJetEvenCoreJet jet k

theorem greenJetJacobiCoreResolventPrefix_succ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (u : ℝ) (N : ℕ) :
    greenJetJacobiCoreResolventPrefix (jet := jet) u (N + 1) =
      greenJetJacobiCoreResolventPrefix (jet := jet) u N +
        u ^ (N + 1) • greenJetEvenCoreJet jet (N + 1) := by
  simp [greenJetJacobiCoreResolventPrefix, Finset.sum_range_succ]

/-- Exact finite resolvent equation with the terminal Jacobi-orbit defect left
visible. -/
theorem greenJetJacobiCoreResolventPrefix_sub_smul_shift
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (u : ℝ) (N : ℕ) :
    greenJetJacobiCoreResolventPrefix (jet := jet) u N -
        u • greenJetJacobiCoreEndomorphism heven
          (greenJetJacobiCoreResolventPrefix (jet := jet) u N) =
      greenJetEvenCoreJet jet 0 -
        u ^ (N + 1) • greenJetEvenCoreJet jet (N + 1) := by
  induction N with
  | zero =>
      simp [greenJetJacobiCoreResolventPrefix]
  | succ N ih =>
      rw [greenJetJacobiCoreResolventPrefix_succ,
        LinearMap.map_add, LinearMap.map_smul,
        greenJetJacobiCoreEndomorphism_jet]
      calc
        greenJetJacobiCoreResolventPrefix u N +
              u ^ (N + 1) • greenJetEvenCoreJet jet (N + 1) -
            u • (greenJetJacobiCoreEndomorphism heven
                (greenJetJacobiCoreResolventPrefix u N) +
              u ^ (N + 1) • greenJetEvenCoreJet jet (N + 1 + 1)) =
            (greenJetJacobiCoreResolventPrefix u N -
                u • greenJetJacobiCoreEndomorphism heven
                  (greenJetJacobiCoreResolventPrefix u N)) +
              (u ^ (N + 1) • greenJetEvenCoreJet jet (N + 1) -
                u • (u ^ (N + 1) •
                  greenJetEvenCoreJet jet (N + 1 + 1))) := by module
        _ = (greenJetEvenCoreJet jet 0 -
                u ^ (N + 1) • greenJetEvenCoreJet jet (N + 1)) +
              (u ^ (N + 1) • greenJetEvenCoreJet jet (N + 1) -
                u • (u ^ (N + 1) •
                  greenJetEvenCoreJet jet (N + 1 + 1))) := by rw [ih]
        _ = greenJetEvenCoreJet jet 0 -
              u ^ (N + 1 + 1) •
                greenJetEvenCoreJet jet (N + 1 + 1) := by
          rw [pow_succ]
          module

/-- The scalar readout of the finite resolvent vector is the corresponding
truncated moment-generating polynomial. -/
theorem inner_greenJetJacobiCoreResolventPrefix_head
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (u : ℝ) (N : ℕ) :
    ⟪(greenJetJacobiCoreResolventPrefix (jet := jet) u N :
        greenJetEvenHilbertSubspace jet),
      greenJetEvenSectorJet jet 0⟫_ℝ =
      ∑ k ∈ Finset.range (N + 1), u ^ k * moments k := by
  unfold greenJetJacobiCoreResolventPrefix
  change
    ⟪(greenJetEvenOperatorCore jet).subtype
        (∑ k ∈ Finset.range (N + 1),
          u ^ k • greenJetEvenCoreJet jet k),
      greenJetEvenSectorJet jet 0⟫_ℝ = _
  rw [map_sum, sum_inner]
  simp only [LinearMap.map_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [real_inner_smul_left
    ((greenJetEvenOperatorCore jet).subtype (greenJetEvenCoreJet jet k))
    (greenJetEvenSectorJet jet 0) (u ^ k)]
  change u ^ k *
    ⟪greenJetEvenSectorJet jet k,
      greenJetEvenSectorJet jet 0⟫_ℝ = _
  rw [inner_greenJetEvenSectorJet_eq_moment hrep]
  simp

/-- The cyclic endomorphism is not an auxiliary shift: after inclusion of its
algebraic domain, it is exactly the restriction of the closed Green
maximal-adjoint square `B* B`. -/
theorem closedGreenJetEnergyAdjointSquare_apply_core_eq_cyclicEndomorphism
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (x : greenJetEvenOperatorCore jet) :
    closedGreenJetEnergyAdjointSquare hrep heven hodd
        (greenJetEvenCoreInClosedAdjointSquareDomain
          hrep heven hodd x) =
      ((greenJetJacobiCoreEndomorphism heven x :
          greenJetEvenOperatorCore jet) :
        greenJetEvenHilbertSubspace jet) := by
  rw [closedGreenJetEnergyAdjointSquare_apply_core]
  exact (greenJetJacobiCoreEndomorphism_coe heven x).symm

/-- In particular, the global Green maximal-adjoint square advances every
vector of the cyclic Jacobi orbit by exactly one jet. -/
theorem closedGreenJetEnergyAdjointSquare_apply_cyclicJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (n : ℕ) :
    closedGreenJetEnergyAdjointSquare hrep heven hodd
        (greenJetEvenCoreInClosedAdjointSquareDomain
          hrep heven hodd (greenJetEvenCoreJet jet n)) =
      greenJetEvenSectorJet jet (n + 1) := by
  rw [closedGreenJetEnergyAdjointSquare_apply_core,
    greenJetJacobiCoreMap_jet]

namespace CompletedNativeGreenWeylHeightCertificate

/-- The complex completed Green kernel, restricted to real scalars. -/
theorem realMomentKernel
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    IsGreenWronskianMomentKernelGramRepresentation moments
      (canonicalCompletedNativeGreenParityJet xiState) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  intro i j
  change greenWronskianMomentKernel moments i j =
    (inner ℂ
      (canonicalCompletedNativeGreenParityJet xiState i)
      (canonicalCompletedNativeGreenParityJet xiState j)).re
  have h := congrArg Complex.re (certificate.greenMomentJets.momentKernel i j)
  simpa [canonicalCompletedNativeGreenParityJet,
    canonicalCompletedNativeNormalizedGreenState] using h

/-- The cyclic moments of the concrete completed Jacobi core equal the
canonical division-free logarithmic moments of the completed native
characteristic. -/
theorem jacobiCyclicMoment_eq_canonicalLogDerivativeMoment
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments)
    (n : ℕ) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    greenJetJacobiCoreCyclicMoment certificate.evenIndependent n =
      canonicalCompletedNativeLogDerivativeMoment n := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  calc
    greenJetJacobiCoreCyclicMoment certificate.evenIndependent n =
        moments n :=
      greenJetJacobiCoreCyclicMoment_eq certificate.realMomentKernel
        certificate.evenIndependent n
    _ = canonicalCompletedNativeLogDerivativeMoment n := by
      rw [completedNativeLogDerivativeMoment_eq_canonical
        certificate.logarithmicMoments]

set_option maxHeartbeats 800000 in
/-- The same cyclic identity after the automatic Hilbert completion used by
the global signed-height construction.  This is the concrete moment seam for
the positive operator whose reciprocal off-diagonal block is the height
operator. -/
theorem completedJacobiCyclicMoment_eq_canonicalLogDerivativeMoment
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments)
    (n : ℕ) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let heven := completedGreenJet_even_linearIndependent
      certificate.evenIndependent
    greenJetJacobiCoreCyclicMoment
        (jet := completedGreenJet
          (canonicalCompletedNativeGreenParityJet xiState)) heven n =
      canonicalCompletedNativeLogDerivativeMoment n := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  calc
    greenJetJacobiCoreCyclicMoment
        (jet := completedGreenJet
          (canonicalCompletedNativeGreenParityJet xiState))
        (completedGreenJet_even_linearIndependent
          certificate.evenIndependent) n = moments n :=
      greenJetJacobiCoreCyclicMoment_eq
        (jet := completedGreenJet
          (canonicalCompletedNativeGreenParityJet xiState))
        (completedGreenJet_gramRepresentation certificate.realMomentKernel)
        (completedGreenJet_even_linearIndependent
          certificate.evenIndependent) n
    _ = canonicalCompletedNativeLogDerivativeMoment n := by
      rw [completedNativeLogDerivativeMoment_eq_canonical
        certificate.logarithmicMoments]

set_option maxHeartbeats 800000 in
/-- The finite cyclic resolvent readout on the completed carrier is exactly
the truncated generating polynomial of the canonical native logarithmic
moments.  Combined with the vector residual theorem above, this is the exact
finite resolvent seam with no discarded terminal term. -/
theorem completedJacobiResolventPrefixScalarReadout_eq_canonical
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments)
    (u : ℝ) (N : ℕ) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ⟪(greenJetJacobiCoreResolventPrefix (jet := jet) u N :
        greenJetEvenHilbertSubspace jet),
      greenJetEvenSectorJet jet 0⟫_ℝ =
      ∑ k ∈ Finset.range (N + 1),
        u ^ k * canonicalCompletedNativeLogDerivativeMoment k := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  rw [inner_greenJetJacobiCoreResolventPrefix_head
    (completedGreenJet_gramRepresentation certificate.realMomentKernel)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [completedNativeLogDerivativeMoment_eq_canonical
    certificate.logarithmicMoments]

set_option maxHeartbeats 800000 in
/-- On the actual completed Green carrier, the positive maximal-adjoint
square used to build the signed-height operator restricts exactly to the
cyclic Jacobi endomorphism. -/
theorem completedEnergyAdjointSquare_apply_core_eq_cyclicEndomorphism
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    ∀ x : greenJetEvenOperatorCore
        (completedGreenJet
          (canonicalCompletedNativeGreenParityJet xiState)),
    let hrep := completedGreenJet_gramRepresentation
      certificate.realMomentKernel
    let heven := completedGreenJet_even_linearIndependent
      certificate.evenIndependent
    let hodd := completedGreenJet_odd_linearIndependent
      certificate.oddIndependent
    closedGreenJetEnergyAdjointSquare hrep heven hodd
        (greenJetEvenCoreInClosedAdjointSquareDomain hrep heven hodd x) =
      ((greenJetJacobiCoreEndomorphism heven x :
          greenJetEvenOperatorCore
            (completedGreenJet
              (canonicalCompletedNativeGreenParityJet xiState))) :
        greenJetEvenHilbertSubspace
          (completedGreenJet
            (canonicalCompletedNativeGreenParityJet xiState))) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  intro x
  exact closedGreenJetEnergyAdjointSquare_apply_core_eq_cyclicEndomorphism
    (completedGreenJet_gramRepresentation certificate.realMomentKernel)
    (completedGreenJet_even_linearIndependent certificate.evenIndependent)
    (completedGreenJet_odd_linearIndependent certificate.oddIndependent) x

/-- Consequently the cyclic Jacobi readout itself satisfies the exact
division-free coefficient identity `q_G * Phi_G = -Phi_G'`. -/
theorem jacobiCyclicMoment_isCompletedNativeLogDerivativeMomentSequence
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    IsCompletedNativeLogDerivativeMomentSequence
      (greenJetJacobiCoreCyclicMoment certificate.evenIndependent) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  have hfun :
      greenJetJacobiCoreCyclicMoment certificate.evenIndependent =
        canonicalCompletedNativeLogDerivativeMoment := by
    funext n
    exact certificate.jacobiCyclicMoment_eq_canonicalLogDerivativeMoment n
  rw [hfun]
  exact canonicalCompletedNativeLogDerivativeMoment_isMomentSequence

set_option maxHeartbeats 800000 in
/-- The cyclic moments of the core inside the completed global operator obey
the completed native coefficient equation itself, not merely a finite-prefix
approximation. -/
theorem completedJacobiCyclicMoment_isCompletedNativeLogDerivativeMomentSequence
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let heven := completedGreenJet_even_linearIndependent
      certificate.evenIndependent
    IsCompletedNativeLogDerivativeMomentSequence
      (greenJetJacobiCoreCyclicMoment
        (jet := completedGreenJet
          (canonicalCompletedNativeGreenParityJet xiState)) heven) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  have hfun :
      greenJetJacobiCoreCyclicMoment
          (jet := completedGreenJet
            (canonicalCompletedNativeGreenParityJet xiState))
          (completedGreenJet_even_linearIndependent
            certificate.evenIndependent) =
        canonicalCompletedNativeLogDerivativeMoment := by
    funext n
    exact certificate.completedJacobiCyclicMoment_eq_canonicalLogDerivativeMoment n
  rw [hfun]
  exact canonicalCompletedNativeLogDerivativeMoment_isMomentSequence

end CompletedNativeGreenWeylHeightCertificate

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.NaturalNativeOperatorShiftCapstone
import CarrySelfAdjointOperator.GreenJetMaximalAdjointSquare
import CarrySelfAdjointOperator.NativeBracketTfvdGreenSameGeometry
import CarrySelfAdjointOperator.CompletedNativeCausalGreenProvenance
import Mathlib.Tactic

/-!
# Native valve/Green energy factor to the finite height operator

This is a source-direction capstone.  The input is the native C2/valve/Green
chain and the strict chiral coefficient gate.  The output records, in order,
the exact tail, the division-free Green coefficient law, its boundary/shift
form, and the fact that the finite Jacobi section is a compression of the
closed Green energy square `B* B`.  The height matrix is only the final
functional-calculus consequence of that section.

No Hankel factorization, fitted spectrum, or operator-to-geometry
reconstruction is used to prove the native response law.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics
open FiniteNativeCarryOperator
open FiniteNativeCarryOperator.Camera
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Camera.FiniteBridge

noncomputable section

theorem canonicalC2Geometry_native_source_valve_green_operator_forced
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ)
    (hdominance : CanonicalCompletedNativeCenteredStrictChiralCoefficientDominance) :
    (∀ (s t : ℂ) (hs : 0 < s.re) (ht : 0 < t.re),
        canonicalCompletedC3RawGammaGram s t hs ht =
          inner ℂ
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase s hs)
            (ContinuousLinearMap.adjoint
              canonicalCompletedC3CausalGreenBoundarySum
              (canonicalCompletedC3CausalGreenBoundarySum
                (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
                  hbase t ht)))) ∧
      (∀ (tailCutoff : ℕ) {s : ℂ}, s ∈ nativeScalarDomain →
        finiteBracketCharacteristic 2 tailCutoff s +
            (∑' index : ℕ,
              centerBracketTerm 2 s (index + tailCutoff)) =
          factor 2 s * nativeScalar s) ∧
      IsPolarizedGreenCoefficientEquation
        canonicalCompletedNativeLogDerivativeMoment
        (fun p q : ℕ ↦
          canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
            M (p + q + 1)) ∧
      ((∀ p : ℕ,
          canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
              M (p + 1) =
            oddMomentResponseCoefficient
              canonicalCompletedNativeLogDerivativeMoment (p + 1)) ∧
        (∀ p q : ℕ,
          canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
              M (p + (q + 1) + 1) =
            canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
              M ((p + 1) + q + 1))) ∧
      ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
        (fun i j : Fin N =>
              ⟪closedGreenJetEnergyAdjointSquare
                  (canonicalCompletedNativeStieltjesJet_momentKernel hpos)
                  (canonicalCompletedNativeStieltjesJet_even_linearIndependent hpos)
                  (canonicalCompletedNativeStieltjesJet_odd_linearIndependent hpos)
                  (canonicalGreenJetEvenAdjointSquareDomainVector
                    (canonicalCompletedNativeStieltjesJet_momentKernel hpos)
                    (canonicalCompletedNativeStieltjesJet_even_linearIndependent hpos)
                    (canonicalCompletedNativeStieltjesJet_odd_linearIndependent hpos)
                    N i),
                (canonicalGreenJetEvenAdjointSquareDomainVector
                  (canonicalCompletedNativeStieltjesJet_momentKernel hpos)
                  (canonicalCompletedNativeStieltjesJet_even_linearIndependent hpos)
                  (canonicalCompletedNativeStieltjesJet_odd_linearIndependent hpos)
                  N j :
                    greenJetEvenHilbertSubspace
                      (canonicalCompletedNativeStieltjesJet hpos))⟫_ℝ) =
            canonicalFiniteJacobiSection
              canonicalCompletedNativeLogDerivativeMoment N
              (canonicalGreenJetHankelGramCertificate
                (canonicalCompletedNativeStieltjesJet_momentKernel hpos)
                (canonicalCompletedNativeStieltjesJet_even_linearIndependent hpos)
                N) ∧
          normalizedCompletedNativeCameraCharacteristic 2 cutoff =
            (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
          completedNativeCameraLogDerivativeMoment 2 cutoff =
            canonicalCompletedNativeLogDerivativeMoment ∧
          (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  rcases canonicalC2Geometry_native_source_valve_green_preGram hbase hradius with
    ⟨_, _, _, htail, _, _, _, _, _, _, _⟩
  have hcoeff :=
    canonicalC2Geometry_nativeWronskianResponse_coefficientEquation_before_gram M
  have hshift :=
    canonicalC2Geometry_nativeWronskianResponse_boundary_and_shift_before_gram M
  have hpos : CanonicalCompletedNativeStieltjesPositivity := by
    have hexpanded :
        CanonicalCompletedC3ExpandedStructuralStrictChiralDominance :=
      (canonicalCompletedNativeCenteredStrictChiralCoefficientDominance_iff_expanded).mp
        hdominance
    exact
      (canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity).mp
        hexpanded
  refine ⟨?_, htail, hcoeff, hshift, ⟨hpos, ?_,
    nativeGeometry_normalizedCamera_eq_commonCharacteristic (camera := 2)
      (by norm_num) cutoff,
    nativeGeometry_cameraMoments_eq_canonical (camera := 2)
      (by norm_num) cutoff,
    nativeGeometryFiniteHeightOperator_isSymm hpos N⟩⟩
  · intro s t hs ht
    exact canonicalCompletedC3RawGammaGram_eq_causalAdjointSquare
      hbase s t hs ht
  · exact closedGreenJetEnergyAdjointSquare_finiteCompression_eq_canonicalSection
      (canonicalCompletedNativeStieltjesJet_momentKernel hpos)
      (canonicalCompletedNativeStieltjesJet_even_linearIndependent hpos)
      (canonicalCompletedNativeStieltjesJet_odd_linearIndependent hpos)
      N

/-! ## Geometric spelling of the same capstone -/

/- The strictness input is exposed in the native expanded chiral carrier,
rather than as an already packaged Stieltjes predicate.  This corollary is
the short source-direction statement to use when the proof arrives from the
orthogonalized camera/Green energy decomposition. -/
theorem canonicalC2Geometry_native_corrected_chiral_height_operator_forced
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ)
    (hdominance : CanonicalCompletedC3ExpandedStructuralStrictChiralDominance) :
    (∀ (tailCutoff : ℕ) {s : ℂ}, s ∈ nativeScalarDomain →
        finiteBracketCharacteristic 2 tailCutoff s +
            (∑' index : ℕ,
              centerBracketTerm 2 s (index + tailCutoff)) =
          factor 2 s * nativeScalar s) ∧
      (∀ p q : ℕ,
        canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M (p + q) =
          polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment p q) ∧
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
  have hforced :=
    canonicalC2Geometry_native_source_valve_green_operator_forced
      hbase hradius M cutoff N
      ((canonicalCompletedNativeCenteredStrictChiralCoefficientDominance_iff_expanded).mpr
        hdominance)
  rcases hforced with ⟨_, htail, _, _, hheight⟩
  rcases hheight with ⟨hpos, _, hnorm, hmom, hsym⟩
  refine ⟨htail, ?_, ?_⟩
  · intro p q
    exact canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_polarizedMoment
      M p q
  · refine ⟨hpos, hnorm, hmom, ?_, hsym⟩
    exact nativeGeometry_cameraJacobiSection_eq_canonical
      (camera := 2) (by norm_num) cutoff N hpos

/-! ## The same-geometry energy capstone

This is the source-side spelling of the construction recorded in the
relational atlas.  The first conjunct keeps the bracket and corrected Green
readouts on one TFVD carrier.  The second keeps the exact whole-centre tail.
The third is the native positive energy identity: causal response plus return
is the original gradient state, so its polarized energy is the adjoint square
of the Green boundary readout.  Only after these identities and the native
boundary/shift law are exposed is the finite height section returned.

No Gram, Cholesky factor, fitted spectrum, or positive proxy is an input to
this theorem.  Strict all-order positivity remains the explicitly named
chiral gate consumed by the last conjunct.
-/
theorem canonicalC2Geometry_native_sameGeometry_energy_to_height_operator
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ)
    (hdominance : CanonicalCompletedNativeCenteredStrictChiralCoefficientDominance) :
    (∀ (cameraCutoff : ℕ) (s : ℂ),
        (finiteSeededEnrichedTfvdGenuineReadout cameraCutoff tfvdHaarScale
            (fun _ : ℕ => (1 : ℂ))
            (canonicalSeededEnrichedTfvdGenuinePort tfvdHaarScale
              (fun _ : ℕ => (1 : ℂ)) s) =
          finiteBracketCharacteristic 3 cameraCutoff s) ∧
        (finiteCanonicalSeededTfvdSameSBoundaryForm cameraCutoff tfvdHaarScale
            (fun _ : ℕ => (1 : ℂ)) s -
          finiteCanonicalTfvdSameSGreenProvenanceDefect 3 cameraCutoff s =
          greenForm
            (finiteC3GenuineBracketGreenBoundaryPair (3 * cameraCutoff) s)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * cameraCutoff) (reflectedParameter s)))) ∧
      (∀ (tailCutoff : ℕ) {s : ℂ}, s ∈ nativeScalarDomain →
        finiteBracketCharacteristic 2 tailCutoff s +
            (∑' index : ℕ,
              centerBracketTerm 2 s (index + tailCutoff)) =
          factor 2 s * nativeScalar s) ∧
      (∀ (s t : ℂ) (hs : 0 < s.re) (ht : 0 < t.re),
        inner ℂ
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase s hs)
            ((canonicalCompletedC3CausalGreenBoundarySum.adjoint)
              (canonicalCompletedC3CausalGreenBoundarySum
                (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
                  hbase t ht))) =
          inner ℂ
            (canonicalCompletedC3DirichletGradientState s hs)
            (canonicalCompletedC3DirichletGradientState t ht)) ∧
      (∀ (s : ℂ) (hs : 0 < s.re),
        carryWeightedVerticalCenteredBracket
            (canonicalBR2CarryAmplitudeRatio base)
            (canonicalCompletedC3DirichletGradientCausalGreenState
              base s hs) =
          canonicalCompletedC3DirichletGradientBracketSourceState
            base s hs) ∧
      IsPolarizedGreenCoefficientEquation
        canonicalCompletedNativeLogDerivativeMoment
        (fun p q : ℕ ↦
          canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
            M (p + q + 1)) ∧
      ((∀ p : ℕ,
          canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
              M (p + 1) =
            oddMomentResponseCoefficient
              canonicalCompletedNativeLogDerivativeMoment (p + 1)) ∧
        (∀ p q : ℕ,
          canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
              M (p + (q + 1) + 1) =
            canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
              M ((p + 1) + q + 1))) ∧
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
  have hforced :=
    canonicalC2Geometry_native_source_valve_green_operator_forced
      hbase hradius M cutoff N hdominance
  rcases hforced with ⟨_, htail, hcoeff, hshift, hheight⟩
  rcases hheight with ⟨hpos, _, hnorm, hmom, hsym⟩
  refine ⟨?_, htail, ?_, ?_, hcoeff, hshift, ?_⟩
  · intro cameraCutoff s
    exact finiteNativeC3BracketTfvdGreen_sameGeometry cameraCutoff s
  · intro s t hs ht
    exact canonicalCompletedC3CausalGreenBoundarySum_adjointSquare_eq_nativeState_inner
      hbase hs ht
  · intro s hs
    exact canonicalCompletedC3CausalGreenBoundary_native_source_response
      hbase hs
  · refine ⟨hpos, hnorm, hmom, ?_, hsym⟩
    exact nativeGeometry_cameraJacobiSection_eq_canonical
      (camera := 2) (by norm_num) cutoff N hpos

/-! The same capstone with the strictness input expressed in the native
radial language. -/

theorem canonicalC2Geometry_native_strictChiralDominance_of_radialLedger
    (hnoLeak : CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound) :
    CanonicalCompletedNativeCenteredStrictChiralCoefficientDominance := by
  apply (canonicalCompletedNativeCenteredStrictChiralCoefficientDominance_iff_expanded).mpr
  apply (canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity).mpr
  exact canonicalCompletedNativeStieltjesPositivity_of_radialLedger
    hnoLeak hstrict

/-! The genuinely energy-level spelling of the same source-direction seam.
The four complex quadratic energies are the polarization of the concrete
radial Gamma/`dslope` jet defect.  This is the useful interface when the
native proof arrives from the valve/Green energy identity rather than from a
kernel no-leak statement. -/

theorem canonicalC2Geometry_native_strictChiralDominance_of_radialJetFlatness
    (hflat : CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeCenteredStrictChiralCoefficientDominance := by
  apply (canonicalCompletedNativeCenteredStrictChiralCoefficientDominance_iff_expanded).mpr
  apply (canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity).mpr
  exact canonicalCompletedNativeStieltjesPositivity_of_radialGammaDslopeJetDefectFlatness
    hflat hnondegenerate

theorem canonicalC2Geometry_native_strictChiralDominance_of_radialQuadraticEnergy
    (henergy : CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeCenteredStrictChiralCoefficientDominance := by
  exact canonicalC2Geometry_native_strictChiralDominance_of_radialJetFlatness
    (canonicalCompletedC3RadialGammaDslopeJetDefectFlatness_of_quadraticEnergy
      henergy)
    hnondegenerate

/-! ## Direct native radial input for the same-geometry energy capstone -/

/-- The same-geometry energy capstone with the strictness input written in
the native radial vocabulary.  The exact bracket/TFVD/Green identities and
the causal adjoint-square identity remain the first fields of the result;
`noLeak` and the uniform Gamma determinant bound are used only to obtain the
strict Stieltjes certificate needed by the final finite height section. -/
abbrev canonicalC2Geometry_native_sameGeometry_energy_to_height_operator_of_radialLedger
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ)
    (hnoLeak : CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound) :=
  canonicalC2Geometry_native_sameGeometry_energy_to_height_operator
    hbase hradius M cutoff N
    (canonicalC2Geometry_native_strictChiralDominance_of_radialLedger
      hnoLeak hstrict)

/-- Energy-level version of the preceding theorem.  The four rotated
quadratic Gamma/dslope energy limits are exactly the polarization data used
to recover the native mixed jet defect; finite nondegeneracy then supplies
the strict part. -/
abbrev canonicalC2Geometry_native_sameGeometry_energy_to_height_operator_of_radialQuadraticEnergy
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ)
    (henergy : CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :=
  canonicalC2Geometry_native_sameGeometry_energy_to_height_operator
    hbase hradius M cutoff N
    (canonicalC2Geometry_native_strictChiralDominance_of_radialQuadraticEnergy
      henergy hnondegenerate)

end

end CarrySelfAdjointOperator

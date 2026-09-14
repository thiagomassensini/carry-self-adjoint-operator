import CarrySelfAdjointOperator.NaturalNativeOperatorShiftCapstone
import CarrySelfAdjointOperator.GreenJetMaximalAdjointSquare
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

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.NaturalNativeOperatorShiftCapstone
import CarrySelfAdjointOperator.GreenJetMaximalAdjointSquare
import CarrySelfAdjointOperator.NativeBracketTfvdGreenSameGeometry
import CarrySelfAdjointOperator.CompletedNativeCausalGreenProvenance
import CarrySelfAdjointOperator.CompletedC3BoundaryRelationSewingBridge
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

open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics
open FiniteNativeCarryOperator
open FiniteNativeCarryOperator.Camera
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open Filter Topology

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

/-! ## Corrected Green/Wronskian normalization -/

/-- The boundary-relation identity gives the native radial readout with the
exact characteristic weight that converts the completed Wronskian into
`dslope`.  This is the division-free algebraic bridge: the weight is retained
explicitly, so the raw Gamma boundary is not confused with the normalized
moment readout. -/
theorem canonicalC2Geometry_native_boundaryGreenSewing_correctedRadialReadout
    (hsewing : CanonicalCompletedC3BoundaryGreenSewing)
    (M : ℕ) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
      canonicalCompletedC3GammaCharacteristicWeight z w *
        ((w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w) := by
  have hzFStar : conj (completedNativeOperatorCharacteristic z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzF
  have hweight : canonicalCompletedC3GammaCharacteristicWeight z w ≠ 0 := by
    unfold canonicalCompletedC3GammaCharacteristicWeight
    exact mul_ne_zero (mul_ne_zero (by norm_num) hzFStar) hwF
  have hdiv :=
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_wronskian_div_weight
      M hzStrip hwStrip hzF hwF
  calc
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z :=
      hsewing.rawWronskian z w hz hw
    _ = canonicalCompletedC3GammaCharacteristicWeight z w *
          canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w := by
      rw [hdiv]
      field_simp [hweight]
    _ = canonicalCompletedC3GammaCharacteristicWeight z w *
          ((w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w) := by
      rw [canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
        M hzStrip hwStrip hzF hwF hsep]

/-- The same seam in the normalized boundary coordinates is exactly the
`dslope` numerator.  This is the form that can be compared with a positive
Gamma Gram; the preceding theorem explains why the raw readout carries the
extra characteristic weight. -/
theorem canonicalC2Geometry_native_boundaryGreenSewing_normalizedRadialReadout
    (hsewing : CanonicalCompletedC3BoundaryGreenSewing)
    (M : ℕ) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout z w hz hw =
      (w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout_eq_kernel,
    hsewing.normalizedGammaKernel_eq_dslope M z w hz hw hzStrip hwStrip hzF hwF
      hsep]

/-! ## Positive native kernel before Hankel

The normalized Green sewing now has a direct Hilbert consequence.  On a
finite radial grid, the completed-native `dslope` kernel is the Gram of the
already constructed normalized Gamma responses.  This transports positivity
from the native Green carrier; it does not define the carrier by a Hankel
factorization or by the height operator.
-/

theorem
    canonicalC2Geometry_native_normalizedRadialDslopeSampleMatrix_posSemidef_of_boundaryGreenSewing
    (hsewing : CanonicalCompletedC3BoundaryGreenSewing)
    (M k N : ℕ)
    (hadmissible : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈ completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (canonicalCompletedNativeRadialDslopeSampleMatrix k N).PosSemidef := by
  have hmatrix :
      canonicalCompletedNativeRadialDslopeSampleMatrix k N =
        Matrix.of (fun i j : Fin N =>
          canonicalCompletedC3NormalizedPolarizedGammaKernel
            (canonicalCompletedC3RadialTiltPoint k i)
            (canonicalCompletedC3RadialTiltPoint k j)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)) := by
    ext i j
    exact
      (hsewing.normalizedGammaKernel_eq_dslope M
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
        (hadmissible i).1 (hadmissible j).1
        (hadmissible i).2 (hadmissible j).2
        (sub_ne_zero.mp
          (canonicalCompletedC3RadialTilt_separation_ne_zero k i j))).symm
  rw [hmatrix]
  exact
    canonicalCompletedC3NormalizedPolarizedGammaKernel_posSemidef
      (point := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i)
      (fun i => canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)

theorem
    canonicalC2Geometry_native_normalizedRadialDslopeSampleMatrix_eventually_posSemidef_of_boundaryGreenSewing
    (hsewing : CanonicalCompletedC3BoundaryGreenSewing)
    (M N : ℕ) :
    ∀ᶠ k : ℕ in (Filter.atTop : Filter ℕ),
      (canonicalCompletedNativeRadialDslopeSampleMatrix k N).PosSemidef := by
  have hadmissible : ∀ᶠ k : ℕ in (Filter.atTop : Filter ℕ), ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈ completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
    refine
      (Filter.eventually_all
        (l := (Filter.atTop : Filter ℕ))
        (p := fun (i : Fin N) k =>
          canonicalCompletedC3RadialTiltPoint k i ∈ completedNativeHeightDomain ∧
            completedNativeOperatorCharacteristic
              (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)).2 ?_
    intro i
    exact canonicalCompletedC3RadialTiltPoint_eventually_admissible i.val
  filter_upwards [hadmissible] with k hk
  exact
    canonicalC2Geometry_native_normalizedRadialDslopeSampleMatrix_posSemidef_of_boundaryGreenSewing
      hsewing M k N hk

/-! ## Normalized radial Gamma jet

The old radial jet in `CompletedNativeRadialTiltSamplePositivity` is the
unnormalized Gamma jet.  The following totalized state keeps the exact
characteristic normalization used by the completed native kernel, while
remaining total on the real axis so that forward differences are legal as
functions on `ℂ`.
-/

def canonicalC2Geometry_nativeNormalizedGammaState (z : ℂ) :
    CarryGammaComplexNaimark :=
  if hz : z.im ≠ 0 then
    canonicalCompletedC3NormalizedPolarizedGammaState z hz
  else 0

@[simp] theorem canonicalC2Geometry_nativeNormalizedGammaState_of_im_ne_zero
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalC2Geometry_nativeNormalizedGammaState z =
      canonicalCompletedC3NormalizedPolarizedGammaState z hz := by
  simp [canonicalC2Geometry_nativeNormalizedGammaState, hz]

def canonicalC2Geometry_nativeNormalizedRadialGammaJet
    (k order : ℕ) : CarryGammaComplexNaimark :=
  completedGreenShiftedForwardDifferenceJet
    canonicalC2Geometry_nativeNormalizedGammaState
    (canonicalCompletedC3RadialSecondStep k) order

def canonicalC2Geometry_nativeNormalizedRadialGammaDslopeJetDefect
    (steps : ℕ × ℕ) (p q : ℕ) : ℂ :=
  inner ℂ
      (canonicalC2Geometry_nativeNormalizedRadialGammaJet steps.1 p)
      (canonicalC2Geometry_nativeNormalizedRadialGammaJet steps.2 q) -
    completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep steps.1)
      (canonicalCompletedC3RadialSecondStep steps.2) p q

theorem
    canonicalC2Geometry_nativeNormalizedRadialGammaDslopeJetDefectFlatness_of_boundaryGreenSewing
    (hsewing : CanonicalCompletedC3BoundaryGreenSewing) :
    ∀ p q : ℕ,
      Tendsto
        (fun steps : ℕ × ℕ =>
          canonicalC2Geometry_nativeNormalizedRadialGammaDslopeJetDefect
            steps p q)
        (Filter.atTop : Filter (ℕ × ℕ)) (nhds 0) := by
  intro p q
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hi : ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (p + 1),
        canonicalCompletedC3RadialTiltPoint k i ∈
            completedNativeHeightDomain ∧
          completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 :=
    (Finset.range (p + 1)).eventually_all.2 fun i hi =>
      canonicalCompletedC3RadialTiltPoint_eventually_admissible i
  have hj : ∀ᶠ k : ℕ in atTop,
      ∀ j ∈ Finset.range (q + 1),
        canonicalCompletedC3RadialTiltPoint k j ∈
            completedNativeHeightDomain ∧
          completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 :=
    (Finset.range (q + 1)).eventually_all.2 fun j hj =>
      canonicalCompletedC3RadialTiltPoint_eventually_admissible j
  have hzero : ∀ᶠ steps : ℕ × ℕ in (Filter.atTop : Filter (ℕ × ℕ)),
      canonicalC2Geometry_nativeNormalizedRadialGammaDslopeJetDefect
        steps p q = 0 := by
    filter_upwards [hfst.eventually hi, hsnd.eventually hj] with
      steps hiSteps hjSteps
    unfold canonicalC2Geometry_nativeNormalizedRadialGammaDslopeJetDefect
      canonicalC2Geometry_nativeNormalizedRadialGammaJet
    rw [inner_completedGreenShiftedForwardDifferenceJet_eq_kernel]
    have hkernel_eq :
        completedGreenKernelTwoStepShiftedForwardDifference
            (fun w z => inner ℂ
              (canonicalC2Geometry_nativeNormalizedGammaState w)
              (canonicalC2Geometry_nativeNormalizedGammaState z))
            (canonicalCompletedC3RadialSecondStep steps.1)
            (canonicalCompletedC3RadialSecondStep steps.2) p q =
          completedGreenKernelTwoStepShiftedForwardDifference
            canonicalCompletedNativePolarizedDslopeKernel
            (canonicalCompletedC3RadialSecondStep steps.1)
            (canonicalCompletedC3RadialSecondStep steps.2) p q := by
      apply completedGreenKernelTwoStepShiftedForwardDifference_eq_of_eq_on_grid
      intro i hii j hjj
      rw [← canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul,
        ← canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
      rw [canonicalC2Geometry_nativeNormalizedGammaState_of_im_ne_zero
          (canonicalCompletedC3RadialTiltPoint steps.1 i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i),
        canonicalC2Geometry_nativeNormalizedGammaState_of_im_ne_zero
          (canonicalCompletedC3RadialTiltPoint steps.2 j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)]
      calc
        inner ℂ
            (canonicalCompletedC3NormalizedPolarizedGammaState
              (canonicalCompletedC3RadialTiltPoint steps.1 i)
              (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i))
            (canonicalCompletedC3NormalizedPolarizedGammaState
              (canonicalCompletedC3RadialTiltPoint steps.2 j)
              (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)) =
          canonicalCompletedC3NormalizedPolarizedGammaKernel
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) :=
              (canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_inner
                _ _ _ _).symm
        _ = canonicalCompletedNativePolarizedDslopeKernel
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j) :=
          hsewing.normalizedGammaKernel_eq_dslope 0 _ _ _ _
            (hiSteps i hii).1 (hjSteps j hjj).1
            (hiSteps i hii).2 (hjSteps j hjj).2
            (sub_ne_zero.mp
              (canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
                steps.1 steps.2 i j))
    rw [hkernel_eq]
    ring
  exact tendsto_nhds_of_eventually_eq hzero

theorem
    canonicalC2Geometry_nativeNormalizedRadialGammaJet_inner_tendsto_of_boundaryGreenSewing
    (hsewing : CanonicalCompletedC3BoundaryGreenSewing) (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ => inner ℂ
        (canonicalC2Geometry_nativeNormalizedRadialGammaJet steps.1 p)
        (canonicalC2Geometry_nativeNormalizedRadialGammaJet steps.2 q))
      atTop
      (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q)) := by
  have hdefect :=
    canonicalC2Geometry_nativeNormalizedRadialGammaDslopeJetDefectFlatness_of_boundaryGreenSewing
      hsewing p q
  have hdslope := completedNativePolarizedDslope_shiftedRadial_tendsto p q
  have hsum := hdefect.add hdslope
  simpa [canonicalC2Geometry_nativeNormalizedRadialGammaDslopeJetDefect] using hsum

theorem canonicalC2Geometry_nativeNormalizedRadialGammaJet_realGram_posSemidef
    {ι : Type*} [Finite ι] (k : ℕ) (order : ι → ℕ) :
    (Matrix.of fun i j =>
      (inner ℂ
        (canonicalC2Geometry_nativeNormalizedRadialGammaJet k (order i))
        (canonicalC2Geometry_nativeNormalizedRadialGammaJet k (order j))).re).PosSemidef := by
  letI : NormedSpace ℝ CarryGammaComplexNaimark :=
    NormedSpace.restrictScalars ℝ ℂ CarryGammaComplexNaimark
  letI : InnerProductSpace ℝ CarryGammaComplexNaimark :=
    InnerProductSpace.rclikeToReal ℂ CarryGammaComplexNaimark
  change (Matrix.gram ℝ (fun i =>
    canonicalC2Geometry_nativeNormalizedRadialGammaJet k (order i))).PosSemidef
  exact Matrix.posSemidef_gram ℝ _

theorem
    canonicalC2Geometry_nativeNormalizedStieltjesPosSemidefinite_of_boundaryGreenSewing
    (hsewing : CanonicalCompletedC3BoundaryGreenSewing) :
    CanonicalCompletedNativeStieltjesPosSemidefinite := by
  intro N
  have hdiag : Tendsto (fun k : ℕ => (k, k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  constructor
  · let evenGram (k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
      Matrix.of fun i j =>
        (inner ℂ
          (canonicalC2Geometry_nativeNormalizedRadialGammaJet k
            (2 * (i : ℕ)))
          (canonicalC2Geometry_nativeNormalizedRadialGammaJet k
            (2 * (j : ℕ)))).re
    apply matrixPosSemidef_of_tendsto_entrywise (A := evenGram)
    · intro k
      exact canonicalC2Geometry_nativeNormalizedRadialGammaJet_realGram_posSemidef
        k (fun i : Fin N => 2 * (i : ℕ))
    · intro i j
      have hcomplex :=
        (canonicalC2Geometry_nativeNormalizedRadialGammaJet_inner_tendsto_of_boundaryGreenSewing
          hsewing (2 * (i : ℕ)) (2 * (j : ℕ))).comp hdiag
      have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
      simpa [evenGram, Function.comp_def, hankelGram,
        completedGreenParityOrder, greenWronskianMomentKernel] using hreal
  · let oddGram (k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
      Matrix.of fun i j =>
        (inner ℂ
          (canonicalC2Geometry_nativeNormalizedRadialGammaJet k
            (2 * (i : ℕ) + 1))
          (canonicalC2Geometry_nativeNormalizedRadialGammaJet k
            (2 * (j : ℕ) + 1))).re
    apply matrixPosSemidef_of_tendsto_entrywise (A := oddGram)
    · intro k
      exact canonicalC2Geometry_nativeNormalizedRadialGammaJet_realGram_posSemidef
        k (fun i : Fin N => 2 * (i : ℕ) + 1)
    · intro i j
      have hcomplex :=
        (canonicalC2Geometry_nativeNormalizedRadialGammaJet_inner_tendsto_of_boundaryGreenSewing
          hsewing (2 * (i : ℕ) + 1) (2 * (j : ℕ) + 1)).comp hdiag
      have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
      simpa [oddGram, Function.comp_def, shiftedHankel,
        completedGreenParityOrder, greenWronskianMomentKernel] using hreal

/-! ## Strictness before the height operator

The normalized Green sewing supplies the semidefinite Hankel pair.  The
incidence transport supplies the independent directions; it is precisely the
separate nondegeneracy input needed to upgrade semidefiniteness to the strict
Stieltjes certificate consumed by the finite height construction.
-/

theorem canonicalC2Geometry_native_strictChiralDominance_of_boundaryGreenSewing
    (hsewing : CanonicalCompletedC3BoundaryGreenSewing)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeCenteredStrictChiralCoefficientDominance := by
  apply (canonicalCompletedNativeCenteredStrictChiralCoefficientDominance_iff_expanded).mpr
  apply (canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity).mpr
  rw [canonicalCompletedNativeStieltjesPositivity_iff_posSemidefinite_and_nondegenerate]
  exact ⟨
    canonicalC2Geometry_nativeNormalizedStieltjesPosSemidefinite_of_boundaryGreenSewing
      hsewing,
    hnondegenerate⟩

/-! ## Same-geometry energy before the height construction -/

/-- The entire native source/energy seam before any positivity or height
object is introduced.  This is the part forced by the C2 bracket, the
completed TFVD port, the exact centre tail, and the causal Green return. -/
theorem canonicalC2Geometry_native_sameGeometry_energy_preHeight
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (M : ℕ) :
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
              M ((p + 1) + q + 1))) := by
  have hcoeff :=
    canonicalC2Geometry_nativeWronskianResponse_coefficientEquation_before_gram M
  have hshift :=
    canonicalC2Geometry_nativeWronskianResponse_boundary_and_shift_before_gram M
  refine ⟨?_, ?_, ?_, ?_, hcoeff, hshift⟩
  · intro cameraCutoff s
    exact finiteNativeC3BracketTfvdGreen_sameGeometry cameraCutoff s
  · intro tailCutoff s hs
    exact canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar
      tailCutoff hs
  · intro s t hs ht
    exact canonicalCompletedC3CausalGreenBoundarySum_adjointSquare_eq_nativeState_inner
      hbase hs ht
  · intro s hs
    exact canonicalCompletedC3CausalGreenBoundary_native_source_response
      hbase hs

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

/-! ## Direct normalized Green input for the same-geometry energy capstone -/

/-- Full source-direction capstone with the remaining boundary identity made
explicit.  The operator is returned only after the Green/valve identities,
the normalized Hilbert carrier, and the independent-incidence strictness have
been supplied. -/
abbrev canonicalC2Geometry_native_sameGeometry_energy_to_height_operator_of_boundaryGreenSewing
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ)
    (hsewing : CanonicalCompletedC3BoundaryGreenSewing)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :=
  canonicalC2Geometry_native_sameGeometry_energy_to_height_operator
    hbase hradius M cutoff N
    (canonicalC2Geometry_native_strictChiralDominance_of_boundaryGreenSewing
      hsewing hnondegenerate)

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

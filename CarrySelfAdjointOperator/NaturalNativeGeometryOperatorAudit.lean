import CarrySelfAdjointOperator.NaturalNativeGreenEnergyOperatorCapstone
import CarrySelfAdjointOperator.CompletedNativeChiralCayleyHerglotz
import CarrySelfAdjointOperator.CompletedC3FullWronskianPolarization
import Mathlib.Tactic

/-!
# Native geometry to height operator: valve audit

This file records the source-direction composition that starts with the
completed radial valve and ends at the finite height operator.  The input is
not a Hankel factorization and is not a fitted spectral datum: it is the
all-order Herglotz/Pick positivity of the completed-native chiral valve,
together with the already isolated incidence nondegeneracy.

The Green/TFVD source, exact tail, causal response-plus-return carrier,
boundary/shift law, and the final finite self-adjoint section are inherited
from `NaturalNativeGreenEnergyCapstone`.  This module only makes the
last natural composition explicit, so the remaining material statement is
visible as one named valve positivity gate.
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

/-- The all-order Herglotz/Pick valve gate supplies the strict native chiral
dominance used by the source-direction Green energy capstone. -/
theorem canonicalC2Geometry_native_strictChiralDominance_of_radialHerglotz
    (hHerglotz :
      CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeCenteredStrictChiralCoefficientDominance := by
  have hcontractive :
      CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive :=
    (canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_herglotz).mpr
      hHerglotz
  apply (canonicalCompletedNativeCenteredStrictChiralCoefficientDominance_iff_expanded).mpr
  apply (canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity).mpr
  exact canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier
    hcontractive hnondegenerate

/-- The direct native geometry-to-height route with the valve written in its
natural Herglotz language.  Its result is the full source-side genealogy:
the bracket/TFVD readout, exact whole-centre tail, causal Green
adjoint-square identity, native polarized coefficient equation, boundary/shift
law, camera-independent characteristic/moments, and the symmetric finite
height operator.

No Gram, Cholesky factor, or preselected operator is used to manufacture the
strictness input: the only positivity input is the completed radial valve
gate above, while nondegeneracy comes from the native incidence construction.
-/
abbrev canonicalC2Geometry_native_sameGeometry_energy_to_height_operator_of_radialHerglotz
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ)
    (hHerglotz :
      CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :=
  canonicalC2Geometry_native_sameGeometry_energy_to_height_operator
    hbase hradius M cutoff N
    (canonicalC2Geometry_native_strictChiralDominance_of_radialHerglotz
      hHerglotz hnondegenerate)

/-! ## The pre-Hankel operator forced by the Green carrier

The global carrier has two retained geometric blocks: the weighted radial
response/return block and the crossed archimedean/chart block.  Both are
symplectic rotations.  The next two lemmas make explicit the operator fact
which is usually hidden when the construction is written directly in scalar
Wronskian notation: the native Green operator is skew-adjoint, and its
canonical quarter-turn is a Hermitian involution.  This is the
orthogonalization step before any moment or Jacobi matrix is named.
-/

theorem inner_canonicalCompletedC3RadialSymplecticRotation_left
    (x y : CanonicalCompletedC3RadialOperatorCarrier) :
    inner ℂ (canonicalCompletedC3RadialSymplecticRotation x) y =
      -inner ℂ x (canonicalCompletedC3RadialSymplecticRotation y) := by
  rw [canonicalCompletedC3RadialSymplecticRotation_apply,
    canonicalCompletedC3RadialSymplecticRotation_apply,
    WithLp.prod_inner_apply]
  change
    inner ℂ (-x.snd) y.fst + inner ℂ x.fst y.snd =
      -(inner ℂ x.fst (-y.snd) + inner ℂ x.snd y.fst)
  rw [inner_neg_left, inner_neg_right]
  ring

theorem inner_canonicalCompletedC3GlobalGreenOperator_left
    (x y : CanonicalCompletedC3GlobalGreenOperatorCarrier) :
    inner ℂ (canonicalCompletedC3GlobalGreenOperator x) y =
      -inner ℂ x (canonicalCompletedC3GlobalGreenOperator y) := by
  rw [canonicalCompletedC3GlobalGreenOperator_apply,
    WithLp.prod_inner_apply]
  change
    inner ℂ
        (canonicalCompletedC3RadialSymplecticRotation x.fst) y.fst +
      inner ℂ (canonicalCompletedC3ArchimedeanChartOperator x.snd) y.snd =
      -(inner ℂ x.fst
          (canonicalCompletedC3RadialSymplecticRotation y.fst) +
        inner ℂ x.snd
          (canonicalCompletedC3ArchimedeanChartOperator y.snd))
  rw [inner_canonicalCompletedC3RadialSymplecticRotation_left,
    inner_canonicalCompletedC3ArchimedeanChartOperator_left]
  ring

theorem canonicalC2Geometry_native_globalGreenOperator_quarterTurn
    (x y : CanonicalCompletedC3GlobalGreenOperatorCarrier) :
    (inner ℂ ((-Complex.I) •
        canonicalCompletedC3GlobalGreenOperator x) y =
      inner ℂ x ((-Complex.I) •
        canonicalCompletedC3GlobalGreenOperator y)) ∧
      ((-Complex.I) • canonicalCompletedC3GlobalGreenOperator
          ((-Complex.I) • canonicalCompletedC3GlobalGreenOperator x) = x) := by
  constructor
  · calc
      inner ℂ ((-Complex.I) •
          canonicalCompletedC3GlobalGreenOperator x) y =
          (starRingEnd ℂ) (-Complex.I) *
            inner ℂ (canonicalCompletedC3GlobalGreenOperator x) y := by
              rw [inner_smul_left]
      _ = Complex.I *
            (-inner ℂ x (canonicalCompletedC3GlobalGreenOperator y)) := by
              rw [inner_canonicalCompletedC3GlobalGreenOperator_left]
              congr 1
              norm_num [Complex.star_def]
      _ = inner ℂ x ((-Complex.I) •
          canonicalCompletedC3GlobalGreenOperator y) := by
              rw [inner_smul_right]
              ring
  · rw [map_smul, smul_smul,
      canonicalCompletedC3GlobalGreenOperator_sq]
    simp

/-! The scalar coefficient remains the native Green response.  This theorem
records the complete source-side order: the geometric operator-valued carrier
is available first, its chiral response supplies the polarized coefficient,
and only the existing incidence/transport certificate is then consumed by the
finite height construction.
-/

theorem canonicalC2Geometry_native_green_operator_to_height
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (M cutoff N : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
    (transport : BR2BracketIncidenceJetTransport base radius
      (polarizedCoefficientParityJet (seededClockAtlasJet block))) :
    (∀ p q : ℕ,
      canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
          M (p + q + 1) =
        polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment p q) ∧
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
  have hchain :=
    canonicalC2Geometry_natural_source_to_height_operator
      hbase hradius M cutoff N block htransport transport
  rcases hchain with
    ⟨_, _, _, _, hcoeff, hheight⟩
  refine ⟨?_, hcoeff, hheight⟩
  intro p q
  exact canonicalCompletedNativeCarryGreenChiralResponse_succCoefficient_eq_polarizedMoment
    M p q

/-! The finite material clock is not needed for the source-direction route.
The shrinking radial Gamma/valve seam is the geometric replacement for that
first-column calibration: its ledger form feeds the already completed
carry/TFVD/Green source capstone, while the uniform determinant bound is kept
as the explicit no-collapse premise. -/

theorem canonicalC2Geometry_native_radial_boundary_to_height
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (cutoff N : ℕ)
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (hstrict :
      CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound) :
    (∀ (tailCutoff : ℕ) {s : ℂ}, s ∈ nativeScalarDomain →
        finiteBracketCharacteristic 2 tailCutoff s +
            (∑' index : ℕ, centerBracketTerm 2 s (index + tailCutoff)) =
          factor 2 s * nativeScalar s) ∧
      (∀ (packagedCutoff : ℕ) (time : ℝ),
        nativeXiCompletionFactor (time : ℂ) *
            completedPackagedFiniteNativeOperatorJet
              2 packagedCutoff 0 time /
              factor 2 (nativeLine time) =
          completedNativeOperatorCharacteristic (time : ℂ)) ∧
      (∀ (M p q : ℕ),
        canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
            M (p + q + 1) =
          polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment p q) ∧
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
  have hnoLeak : CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak :=
    (canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_iff_ledgerNoLeak).mp
      hboundary
  exact
    canonicalC2Geometry_native_source_valve_green_to_height_of_radialLedger
      hbase hradius hnoLeak hstrict cutoff N

end

end CarrySelfAdjointOperator

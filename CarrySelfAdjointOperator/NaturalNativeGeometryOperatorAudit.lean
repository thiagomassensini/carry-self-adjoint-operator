import CarrySelfAdjointOperator.NaturalNativeGreenEnergyOperatorCapstone
import CarrySelfAdjointOperator.CompletedNativeChiralCayleyHerglotz
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

end

end CarrySelfAdjointOperator

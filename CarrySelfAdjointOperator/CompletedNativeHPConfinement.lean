import CarrySelfAdjointOperator.CompletedNativeComplexGraphResolvent
import CarrySelfAdjointOperator.LinearPMapMeromorphicResolvent
import Mathlib.Tactic

/-!
# Hilbert--Polya confinement for the completed native operator

This module isolates the exact operator-theoretic implication in the
completed native route.  It uses the concrete completed Green carrier and
the positive Jacobi operator already constructed from a
`CompletedNativeGreenWeylReducedHeightCertificate`.

The local graph resolvent and its native logarithmic-derivative readout are
already theorems of `CompletedNativeComplexGraphResolvent`.  The only global
interface retained here says that this same vector graph equation continues
to the selected height and that its bounded scalar readout is the canonical
global native Weyl continuation.

At a native zero, the scalar readout has a pole.  Closedness of the graph
then produces the eigenvalue `(z^2)⁻¹` of the positive self-adjoint Jacobi
operator.  Reality and nonnegativity of that eigenvalue force `z` to be real.
-/

open Filter Topology

namespace CarrySelfAdjointOperator

noncomputable section

/-- If the inverse square of a nonzero complex height is real and
nonnegative, then the height itself is real. -/
theorem complex_im_eq_zero_of_sq_inv_real_nonneg
    {z : ℂ} (hz : z ≠ 0)
    (him : (z ^ 2)⁻¹.im = 0)
    (hre : 0 ≤ (z ^ 2)⁻¹.re) :
    z.im = 0 := by
  have hsqNe : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hnormPos : 0 < Complex.normSq (z ^ 2) :=
    Complex.normSq_pos.mpr hsqNe
  have hsqImZero : (z ^ 2).im = 0 := by
    rw [Complex.inv_im] at him
    have hneg : -(z ^ 2).im = 0 :=
      (div_eq_zero_iff).mp him |>.resolve_right (ne_of_gt hnormPos)
    exact neg_eq_zero.mp hneg
  by_contra hzim
  have hproduct : z.re * z.im = 0 := by
    rw [pow_two, Complex.mul_im] at hsqImZero
    nlinarith
  have hzre : z.re = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right hzim
  have hsqReNeg : (z ^ 2).re < 0 := by
    rw [pow_two, Complex.mul_re, hzre]
    nlinarith [sq_pos_of_ne_zero hzim]
  have hinvReNeg : (z ^ 2)⁻¹.re < 0 := by
    rw [Complex.inv_re]
    exact div_neg_of_neg_of_pos hsqReNeg hnormPos
  linarith

namespace CompletedNativeGreenWeylReducedHeightCertificate

open ComplexifiedOrbitResolvent

variable {Hxi : Type*}
variable [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
variable {xiState : ℂ → Hxi} {moments : ℕ → ℝ}

@[reducible] local instance completedNativeHPAmbientRealInnerProductSpace :
    InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance completedNativeHPJacobiEvenCarrierCompleteSpace :
    CompleteSpace (CompletedJacobiEvenCarrier xiState) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJacobiGreenJet xiState)).completeSpace_coe

/-- The concrete positive Jacobi operator, bundled with its maximal real
self-adjointness data. -/
def completedJacobiEnergySelfAdjointData
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    LinearPMap.RealMaximalSelfAdjointData
      (CompletedJacobiEvenCarrier xiState) :=
  { operator := certificate.completedJacobiEnergyOperator
    denseDomain := closedGreenJetEnergyAdjointSquare_dense_domain
      (completedGreenJet_gramRepresentation certificate.realMomentKernel)
      (completedGreenJet_even_linearIndependent certificate.evenIndependent)
      (completedGreenJet_odd_linearIndependent certificate.oddIndependent)
    adjoint_eq := closedGreenJetEnergyAdjointSquare_isMaximalRealSelfAdjoint
      (completedGreenJet_gramRepresentation certificate.realMomentKernel)
      (completedGreenJet_even_linearIndependent certificate.evenIndependent)
      (completedGreenJet_odd_linearIndependent certificate.oddIndependent) }

/-- Positivity of the concrete completed Jacobi operator on its full natural
domain. -/
theorem completedJacobiEnergyOperator_inner_nonneg
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments)
    (x : certificate.completedJacobiEnergyOperator.domain) :
    0 ≤ inner ℝ (certificate.completedJacobiEnergyOperator x)
      (x : CompletedJacobiEvenCarrier xiState) := by
  exact closedGreenJetEnergyAdjointSquare_inner_nonneg
    (completedGreenJet_gramRepresentation certificate.realMomentKernel)
    (completedGreenJet_even_linearIndependent certificate.evenIndependent)
    (completedGreenJet_odd_linearIndependent certificate.oddIndependent) x

/-- Exact global continuation interface for the already-constructed local
graph resolvent.  No new carrier or auxiliary operator occurs here: the graph
is that of the complexification of the same concrete positive Jacobi
operator, and the scalar component is the canonical native Weyl continuation.
-/
def HasGlobalGraphResolventAt
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments)
    (z₀ : ℂ) : Prop :=
  let E := CompletedJacobiEvenCarrier xiState
  let data := certificate.completedJacobiEnergySelfAdjointData
  ∃ (graphResolvent : ℂ →
        RealHilbertComplexification E × RealHilbertComplexification E)
      (source : RealHilbertComplexification E)
      (readout :
        (RealHilbertComplexification E ×
          RealHilbertComplexification E) →L[ℂ] ℂ),
    MeromorphicAt graphResolvent z₀ ∧
      (∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        graphResolvent z ∈ data.complexification.graph) ∧
      (∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        (graphResolvent z).1 - z ^ 2 • (graphResolvent z).2 = source) ∧
      (∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        readout (graphResolvent z) =
          completedNativeJacobiWeylHeightContinuation z)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- At a native zero, global continuation of the concrete graph resolvent
produces the reciprocal-square point eigenvalue of the positive Jacobi
operator.  This is the exact zero-to-spectrum arrow of the HP route. -/
theorem completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_of_globalGraphResolvent
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments)
    {z₀ : ℂ}
    (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hglobal : certificate.HasGlobalGraphResolventAt z₀) :
    LinearPMap.HasEigenvalue
      certificate.completedJacobiEnergySelfAdjointData.complexification
      (z₀ ^ 2)⁻¹ := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  rcases hglobal with
    ⟨graphResolvent, source, readout, hmeromorphic,
      hgraph, hresolvent, hreadout⟩
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  have hreadoutCobounded :
      Tendsto (fun z => readout (graphResolvent z))
        (nhdsWithin z₀ {z₀}ᶜ) (Bornology.cobounded ℂ) := by
    have hreadoutSymm : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        completedNativeJacobiWeylHeightContinuation z =
          readout (graphResolvent z) := by
      filter_upwards [hreadout] with z hz
      exact hz.symm
    exact
      (completedNativeJacobiWeylHeightContinuation_tendsto_cobounded_at_nativeZero
        hzDomain hzero).congr' hreadoutSymm
  exact
    LinearPMap.hasEigenvalue_inv_parameter_of_meromorphic_graphResolvent_readout
      data.complexification data.complexification_isClosed
      (parameter := fun z : ℂ => z ^ 2)
      (by fun_prop) (pow_ne_zero 2 hz₀)
      hmeromorphic readout hreadoutCobounded hgraph hresolvent

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- Hilbert--Polya implication for the completed native operator.  Once the
local vector graph resolvent is continued through the named global interface,
every zero of the native characteristic in its natural height domain has
real centered height. -/
theorem zero_im_eq_zero_of_globalGraphResolvent
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments)
    {z₀ : ℂ}
    (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hglobal : certificate.HasGlobalGraphResolventAt z₀) :
    z₀.im = 0 := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  have heigen :
      LinearPMap.HasEigenvalue data.complexification (z₀ ^ 2)⁻¹ := by
    exact certificate.completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_of_globalGraphResolvent
      hzDomain hzero hglobal
  have hspectrum :=
    data.complexification_eigenvalue_real_nonneg
      (certificate.completedJacobiEnergyOperator_inner_nonneg) heigen
  exact complex_im_eq_zero_of_sq_inv_real_nonneg
    hz₀ hspectrum.1 hspectrum.2

end CompletedNativeGreenWeylReducedHeightCertificate

end

end CarrySelfAdjointOperator

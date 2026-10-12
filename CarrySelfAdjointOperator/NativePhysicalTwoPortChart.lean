import CarrySelfAdjointOperator.NativePhysicalEndpointEncoder
import CarrySelfAdjointOperator.NativeCauchyLaguerreSignedPairing
import CarrySelfAdjointOperator.NativeCompletedFiniteGreenResidual

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators ComplexConjugate InnerProductSpace
open ChiralReturn NativeLaguerre
noncomputable section
set_option autoImplicit false

def portHalfNormalization : ℂ := (Real.sqrt 2 : ℂ)⁻¹

theorem portHalfNormalization_sq : portHalfNormalization ^ 2 = (2 : ℂ)⁻¹ := by
  have hs : (Real.sqrt 2 : ℂ)^2 = (2 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold portHalfNormalization
  rw [inv_pow, hs]

theorem portHalfNormalization_star : star portHalfNormalization = portHalfNormalization := by
  simp [portHalfNormalization]

/-- A whole ambient pair, with both polynomial ports kept. -/
def twoPortReconstruct (p : CanonicalCompletedNativeProjectiveChiralCarrier) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  (portHalfNormalization • (p.2+Complex.I • p.1),
   portHalfNormalization • (p.2-Complex.I • p.1))

def twoPortChart (f : CanonicalCompletedNativeProjectiveChiralCarrier) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  (portHalfNormalization • (-Complex.I • (f.1-f.2)),
   portHalfNormalization • (f.1+f.2))

theorem twoPortChart_reconstruct (p : CanonicalCompletedNativeProjectiveChiralCarrier) :
    twoPortChart (twoPortReconstruct p) = p := by
  have hs : portHalfNormalization * portHalfNormalization = (2 : ℂ)⁻¹ := by
    simpa only [pow_two] using portHalfNormalization_sq
  apply Prod.ext
  · change portHalfNormalization • (-Complex.I •
      (portHalfNormalization • (p.2+Complex.I • p.1) -
       portHalfNormalization • (p.2-Complex.I • p.1))) = p.1
    rw [← smul_sub, smul_comm (-Complex.I), smul_smul, hs]
    simp only [smul_sub, smul_add, smul_smul, neg_mul, Complex.I_mul_I]
    module
  · change portHalfNormalization •
      (portHalfNormalization • (p.2+Complex.I • p.1) +
       portHalfNormalization • (p.2-Complex.I • p.1)) = p.2
    rw [← smul_add, smul_smul, hs]
    module

theorem twoPortReconstruct_chart (f : CanonicalCompletedNativeProjectiveChiralCarrier) :
    twoPortReconstruct (twoPortChart f) = f := by
  have hs : portHalfNormalization * portHalfNormalization = (2 : ℂ)⁻¹ := by
    simpa only [pow_two] using portHalfNormalization_sq
  apply Prod.ext <;>
    simp only [twoPortReconstruct, twoPortChart]
  · rw [smul_comm Complex.I, ← smul_add, smul_smul, hs]
    simp only [smul_sub, smul_smul, mul_neg, Complex.I_mul_I]
    module
  · rw [smul_comm Complex.I, ← smul_sub, smul_smul, hs]
    simp only [smul_sub, smul_smul, mul_neg, Complex.I_mul_I]
    module

def twoPortSynthesis (N k : ℕ) (v s : Fin N → ℂ) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  twoPortReconstruct (radialIncidentSynthesis k N v, radialIncidentSynthesis k N s)

theorem twoPortSynthesis_chart (N k : ℕ) (v s : Fin N → ℂ) :
    twoPortChart (twoPortSynthesis N k v s) =
      (radialIncidentSynthesis k N v, radialIncidentSynthesis k N s) :=
  twoPortChart_reconstruct _

theorem twoPortSynthesis_injective (N k : ℕ) :
    Function.Injective (fun p : (Fin N → ℂ) × (Fin N → ℂ) => twoPortSynthesis N k p.1 p.2) := by
  intro p t h
  have he := congrArg twoPortChart h
  rw [twoPortSynthesis_chart, twoPortSynthesis_chart] at he
  exact Prod.ext (radialIncidentSynthesis_injective k N (congrArg Prod.fst he))
    (radialIncidentSynthesis_injective k N (congrArg Prod.snd he))

def twoPortEndpointEncoding (N k : ℕ) (v s : Fin N → ℂ) : (Fin N → ℂ) × (Fin N → ℂ) :=
  (physicalEndpointJetInput N k v, physicalEndpointJetInput N k s)

def twoPortEndpointReconstruction (N k : ℕ) (x y : Fin N → ℂ) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  twoPortSynthesis N k (decodedEndpointCoefficients N k x) (decodedEndpointCoefficients N k y)

/-- Endpoint coordinates recover the entire finite ambient pair, also
outside the source graph and in its diagonal residual channel. -/
theorem twoPortEndpoint_reconstruct_entire_pair (N k : ℕ) (v s : Fin N → ℂ) :
    twoPortEndpointReconstruction N k (twoPortEndpointEncoding N k v s).1
      (twoPortEndpointEncoding N k v s).2 = twoPortSynthesis N k v s := by
  simp only [twoPortEndpointReconstruction, twoPortEndpointEncoding,
    decodedEndpointCoefficients_encode]

theorem twoPort_signed_form (N k : ℕ) (v s w t : Fin N → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v s) (twoPortSynthesis N k w t) =
      (Complex.I*((k : ℂ)+1)/2) *
        (matrixPairing (cauchyMatrix N) s w - matrixPairing (cauchyMatrix N) v t) := by
  unfold twoPortSynthesis twoPortReconstruct canonicalCompletedNativeProjectiveChiralForm
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  rw [show conj portHalfNormalization = portHalfNormalization by
    simpa only [RCLike.star_def] using portHalfNormalization_star]
  simp only [Complex.conj_I, incident_inner_eq_matrixPairing]
  have hs := portHalfNormalization_sq
  rw [pow_two] at hs
  linear_combination
    Complex.I * ((k : ℂ)+1) *
      (matrixPairing (cauchyMatrix N) s w - matrixPairing (cauchyMatrix N) v t) * hs

def originalResponse (z : ℂ) : ℂ :=
  -deriv completedNativeOperatorCharacteristic z / completedNativeOperatorCharacteristic z

theorem normalized_chiral_twoPorts (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z ≠ 0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0) :
    completedNativeNormalizedPositiveChiralAmplitude z =
        portHalfNormalization * (originalResponse z+Complex.I) ∧
    completedNativeNormalizedPositiveChiralAmplitude z *
        completedNativeHermiteBiehlerChiralQuotient z =
        portHalfNormalization * (originalResponse z-Complex.I) := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  constructor
  · unfold completedNativeNormalizedPositiveChiralAmplitude
      canonicalCompletedC3FullWronskianChiralNormalization
      completedNativePositiveHermiteBiehlerCoordinate portHalfNormalization originalResponse
    field_simp
  · unfold completedNativeNormalizedPositiveChiralAmplitude
      completedNativeHermiteBiehlerChiralQuotient
    rw [mul_assoc, mul_div_cancel₀ _ hP]
    unfold canonicalCompletedC3FullWronskianChiralNormalization
      completedNativeNegativeHermiteBiehlerCoordinate portHalfNormalization originalResponse
    field_simp

theorem normalized_chiral_gap_and_response (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z ≠ 0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0) :
    completedNativeNormalizedPositiveChiralAmplitude z -
      completedNativeNormalizedPositiveChiralAmplitude z *
        completedNativeHermiteBiehlerChiralQuotient z = (Real.sqrt 2 : ℂ)*Complex.I ∧
    (completedNativeNormalizedPositiveChiralAmplitude z +
      completedNativeNormalizedPositiveChiralAmplitude z *
        completedNativeHermiteBiehlerChiralQuotient z) / (Real.sqrt 2 : ℂ) = originalResponse z := by
  have hs : (Real.sqrt 2 : ℂ)^2 = (2 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [(normalized_chiral_twoPorts z hF hP).2, (normalized_chiral_twoPorts z hF hP).1]
  unfold portHalfNormalization
  constructor
  · field_simp
    linear_combination -Complex.I*hs
  · field_simp
    linear_combination -originalResponse z*hs

def radialResponse (N k : ℕ) : Fin N → ℂ :=
  fun j => originalResponse (canonicalCompletedC3RadialTiltPoint k j)

theorem finiteProjectiveSource_eq_twoPorts (N k : ℕ) (v : Fin N → ℂ)
    (hreg : ∀ j : Fin N,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    finiteProjectiveSource N k v =
      twoPortSynthesis N k v (fun j => radialResponse N k j * v j) := by
  apply Prod.ext <;>
    simp only [finiteProjectiveSource, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      canonicalCompletedNativeRadialProjectiveChiralState, canonicalCompletedNativeRadialChiralDefectState,
      completedNativeRadialChiralMultiplierState, smul_smul,
      twoPortSynthesis, twoPortReconstruct, radialIncidentSynthesis,
      LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
  · apply Finset.sum_congr rfl
    intro j _
    rw [(normalized_chiral_twoPorts _ (hreg j).1 (hreg j).2).1]
    simp only [smul_add, smul_smul, radialResponse]
    module
  · apply Finset.sum_congr rfl
    intro j _
    have hb := (normalized_chiral_twoPorts _ (hreg j).1 (hreg j).2).2
    simp only [smul_sub, smul_smul, radialResponse]
    rw [mul_assoc (v j), hb]
    module

end
end CarrySelfAdjointOperator.PhysicalSewing

import CarrySelfAdjointOperator.NativePhysicalFiniteSewing

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators unitInterval
open Polynomial NativeCauchyPorts NativeLaguerre
open NativeCarrySpectralWeyl.Camera.FiniteBridge
noncomputable section
set_option autoImplicit false

def materialStencilRadialCoefficients : FormalStencil →ₗ[ℤ] (ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℤ (fun m => if m = 0 then 0 else Finsupp.single (m-1) (1 : ℂ))

/-- The literal positive-position lift applied to the completed columns. -/
def originalMaterialCompletedSource (k : ℕ) :
    FormalStencil →ₗ[ℤ] CanonicalCompletedNativeProjectiveChiralCarrier :=
  Finsupp.linearCombination ℤ (fun m => if m = 0 then 0 else
    canonicalCompletedNativeRadialProjectiveChiralState k (m-1))

theorem originalMaterialCompletedSource_eq_physical (k : ℕ) (s : FormalStencil) :
    originalMaterialCompletedSource k s =
      physicalCompletedFiniteSource k (materialStencilRadialCoefficients s) := by
  have he : originalMaterialCompletedSource k =
      ((Finsupp.linearCombination ℂ (canonicalCompletedNativeRadialProjectiveChiralState k)).restrictScalars ℤ).comp
        materialStencilRadialCoefficients := by
    apply Finsupp.lhom_ext
    intro m c
    simp only [LinearMap.coe_comp, Function.comp_apply,
      materialStencilRadialCoefficients, originalMaterialCompletedSource,
      Finsupp.linearCombination_single, LinearMap.restrictScalars_apply, map_smul]
    split_ifs with hm
    · simp
    · simp
  rw [he, LinearMap.comp_apply, physicalCompletedFiniteSource_original]
  rfl

theorem materialStencilRadialCoefficients_eq_fin (s : FormalStencil) :
    materialStencilRadialCoefficients s =
      finRadialCoefficients (2*materialStencilHalfWindow s) (materialStencilCoefficients s) := by
  ext j
  rw [finRadialCoefficients_coeff, materialStencilCoefficients_polynomial]
  have he : ((Finsupp.lapply (R := ℂ) (M := ℂ) j).restrictScalars ℤ).comp materialStencilRadialCoefficients =
      ((Polynomial.lcoeff ℂ j).restrictScalars ℤ).comp materialStencilPolynomial := by
    apply Finsupp.lhom_ext
    intro m c
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      materialStencilRadialCoefficients, materialStencilPolynomial,
      Finsupp.linearCombination_single, map_smul, Finsupp.lapply_apply, Polynomial.lcoeff_apply]
    split_ifs with hm
    · simp
    · simp [Finsupp.single_apply, Polynomial.coeff_monomial]
  exact congrArg (fun f => f s) he

/-- The material producer, SourceJet, and corrected Green identify the
same whole pair BEFORE pairing or observation. -/
theorem originalMaterial_wholeSource_capstone (k : ℕ) (s : FormalStencil)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    nativeSourceProjectiveBoundaryJetSynthesis (materialStencilHalfWindow s) k
        (physicalEndpointJetInput (2*materialStencilHalfWindow s) k (materialStencilCoefficients s)) =
      originalMaterialCompletedSource k s ∧
    originalMaterialCompletedSource k s =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k (materialStencilRadialCoefficients s) +
          physicalGreenResidualNumerator q k (materialStencilRadialCoefficients s)) := by
  rw [originalMaterialCompletedSource_eq_physical, materialStencilRadialCoefficients_eq_fin,
    physicalCompletedFiniteSource_fin]
  exact physicalFiniteSewing_capstone _ k _ q hq0 hq1

theorem originalMaterialCompletedSource_atom (k j : ℕ) :
    originalMaterialCompletedSource k (atom (j+1)) =
      canonicalCompletedNativeRadialProjectiveChiralState k j := by
  simp [originalMaterialCompletedSource, atom]

theorem originalMaterialCompletedSource_bracket (k p r : ℕ) :
    originalMaterialCompletedSource k (centeredBracketStencil (p+r+1) r) =
      canonicalCompletedNativeRadialProjectiveChiralState k p -
        (2 : ℂ) • canonicalCompletedNativeRadialProjectiveChiralState k (p+r) +
        canonicalCompletedNativeRadialProjectiveChiralState k (p+2*r) := by
  have hl : p+r+1-r = p+1 := by omega
  have hr : p+r+1+r = (p+2*r)+1 := by omega
  rw [centeredBracketStencil, map_add, map_sub, map_nsmul, hl, hr,
    originalMaterialCompletedSource_atom, originalMaterialCompletedSource_atom,
    originalMaterialCompletedSource_atom]
  norm_cast

theorem originalMaterialCompletedSource_camera (k b M : ℕ) :
    originalMaterialCompletedSource k (finiteStencil b M) =
      originalMaterialCompletedSource k (seedStencil b) +
        ∑ a ∈ Finset.range M, originalMaterialCompletedSource k (centerStencil b a) := by
  simp [finiteStencil]

def polynomialIntervalRepresentative (p : ℂ[X]) : C(unitInterval, ℂ) :=
  ⟨fun u => p.eval ((u : ℝ) : ℂ), p.continuous.comp (Complex.continuous_ofReal.comp continuous_subtype_val)⟩

/-- The same representative as the existing independent Cauchy material
profile, including its half density. -/
theorem materialStencilPolynomial_matches_originalProfile (k : ℕ) (s : FormalStencil) :
    nativeStencilCauchyProfile k s =
      radialContinuousState k 0 * polynomialIntervalRepresentative (materialStencilPolynomial s) := by
  let L : ℂ[X] →ₗ[ℤ] C(unitInterval, ℂ) :=
    { toFun := fun p => radialContinuousState k 0 * polynomialIntervalRepresentative p
      map_add' := by intro p t; ext u; simp [polynomialIntervalRepresentative, mul_add]
      map_smul' := by
        intro c p
        ext u
        simp [polynomialIntervalRepresentative, mul_left_comm] }
  have he : nativeStencilCauchyProfile k = L.comp materialStencilPolynomial := by
    apply Finsupp.lhom_ext
    intro m c
    simp only [nativeStencilCauchyProfile, materialStencilPolynomial, Finsupp.linearCombination_single,
      LinearMap.comp_apply, map_smul]
    split_ifs with hm
    · ext u
      simp [L, polynomialIntervalRepresentative]
    · congr 1
      ext u
      simp [L, polynomialIntervalRepresentative, Polynomial.eval_monomial,
        radialContinuousState, completedNativeChiralCauchyContinuousFeature,
        mul_assoc, Complex.ofReal_mul, Complex.ofReal_pow]
  exact congrArg (fun f => f s) he

/-- The derivative input polynomial is the original all-distance material
profile, not a coefficient vector selected from the desired output. -/
theorem originalMaterialBracket_profile_provenance (k p r : ℕ) :
    radialContinuousState k 0 *
      polynomialIntervalRepresentative (materialStencilPolynomial (centeredBracketStencil (p+r+1) r)) =
        radialContinuousState k p * (1-intervalCoordinate^r)^2 := by
  rw [← materialStencilPolynomial_matches_originalProfile, nativeBracket_profile_factor]

theorem originalMaterialCamera_profile_provenance (k b M : ℕ) :
    radialContinuousState k 0 *
      polynomialIntervalRepresentative (materialStencilPolynomial (finiteStencil b M)) =
        nativeStencilCauchyProfile k (seedStencil b) +
          ∑ a ∈ Finset.range M, nativeStencilCauchyProfile k (centerStencil b a) := by
  rw [← materialStencilPolynomial_matches_originalProfile, nativeCamera_profile_seed_centers]

end
end CarrySelfAdjointOperator.PhysicalSewing

import CarrySelfAdjointOperator.NativePhysicalTwoPortChart
import CarrySelfAdjointOperator.NativePhysicalEndpointCompletion
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSourceTrace

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators
open CPFormal.Analytic.Cp ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Both tails are joined only in the readout; the enriched state remains
the domain, with transport and its original Green port intact. -/
def tfvdStateTracePair {M : ℕ} (z : ℂ) (state : CanonicalC3BracketTfvdCompletionState M) : ℂ × ℂ :=
  (nativeXiCompletionFactor z * (state.valueReadout / cpChartFactor 3 (operatorHeightParameter z)),
   nativeXiCompletionBoundaryCompanion z *
      (state.valueReadout / cpChartFactor 3 (operatorHeightParameter z)) +
     nativeXiCompletionFactor z * Complex.I *
       ((state.logJetReadout * cpChartFactor 3 (operatorHeightParameter z) +
         state.valueReadout * deriv (cpChartFactor 3) (operatorHeightParameter z)) /
           cpChartFactor 3 (operatorHeightParameter z)^2))

theorem tfvdStateTracePair_canonical (M : ℕ) (z : ℂ) :
    tfvdStateTracePair z (canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z)) =
      canonicalC3BracketTfvdCompletedTracePair M z := by
  apply Prod.ext
  · rfl
  · unfold tfvdStateTracePair canonicalC3BracketTfvdCompletedTracePair
      canonicalC3BracketTfvdBoundaryCompanion canonicalC3BracketTfvdNormalizedLogJetReadout
      canonicalC3BracketTfvdNormalizedValueReadout
    ring

def tfvdStateResponse {M : ℕ} (z : ℂ) (state : CanonicalC3BracketTfvdCompletionState M) : ℂ :=
  (tfvdStateTracePair z state).2 / (tfvdStateTracePair z state).1

theorem tfvdStateResponse_threeChannels {M : ℕ} (z : ℂ)
    (state : CanonicalC3BracketTfvdCompletionState M)
    (hQ : cpChartFactor 3 (operatorHeightParameter z) ≠ 0)
    (hXi : nativeXiCompletionFactor z ≠ 0) (hT : state.valueReadout ≠ 0) :
    tfvdStateResponse z state =
      nativeXiCompletionBoundaryCompanion z / nativeXiCompletionFactor z +
        Complex.I * deriv (cpChartFactor 3) (operatorHeightParameter z) /
          cpChartFactor 3 (operatorHeightParameter z) +
        Complex.I * state.logJetReadout / state.valueReadout := by
  unfold tfvdStateResponse tfvdStateTracePair
  field_simp
  ring

theorem tfvdStateResponse_divisionFree {M : ℕ} (z : ℂ)
    (state : CanonicalC3BracketTfvdCompletionState M)
    (hQ : cpChartFactor 3 (operatorHeightParameter z) ≠ 0)
    (hXi : nativeXiCompletionFactor z ≠ 0) (hT : state.valueReadout ≠ 0) :
    nativeXiCompletionFactor z * cpChartFactor 3 (operatorHeightParameter z) *
        state.valueReadout * tfvdStateResponse z state -
      nativeXiCompletionBoundaryCompanion z * cpChartFactor 3 (operatorHeightParameter z) *
        state.valueReadout -
      Complex.I * nativeXiCompletionFactor z *
        (state.logJetReadout * cpChartFactor 3 (operatorHeightParameter z) +
          state.valueReadout * deriv (cpChartFactor 3) (operatorHeightParameter z)) = 0 := by
  rw [tfvdStateResponse_threeChannels z state hQ hXi hT]
  field_simp
  ring

theorem tfvdCanonicalResponse_eq_original (M : ℕ) (z : ℂ)
    (hstrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (_hF : completedNativeOperatorCharacteristic z ≠ 0) :
    tfvdStateResponse z (canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z)) =
      originalResponse z := by
  unfold tfvdStateResponse
  rw [tfvdStateTracePair_canonical, canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M hstrip]
  rfl

theorem tfvdCanonicalResponse_regular_denominators (M : ℕ) (z : ℂ)
    (hstrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    cpChartFactor 3 (operatorHeightParameter z) ≠ 0 ∧
    nativeXiCompletionFactor z ≠ 0 ∧
    (canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z)).valueReadout ≠ 0 := by
  have he := congrArg Prod.fst (canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M hstrip)
  have hval : nativeXiCompletionFactor z *
      ((canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z)).valueReadout /
        cpChartFactor 3 (operatorHeightParameter z)) ≠ 0 := by
    change canonicalC3BracketTfvdCompletedValueReadout M z ≠ 0
    change canonicalC3BracketTfvdCompletedValueReadout M z = completedNativeOperatorCharacteristic z at he
    rw [he]
    exact hF
  exact ⟨cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hstrip,
    (mul_ne_zero_iff.mp hval).1,
    (div_ne_zero_iff.mp (mul_ne_zero_iff.mp hval).2).1⟩

def tfvdStateHeadResponse {M : ℕ} (z : ℂ) (state : CanonicalC3BracketTfvdCompletionState M) : ℂ :=
  nativeXiCompletionBoundaryCompanion z / nativeXiCompletionFactor z +
    Complex.I * deriv (cpChartFactor 3) (operatorHeightParameter z) /
      cpChartFactor 3 (operatorHeightParameter z) +
    Complex.I * state.transport.logJetReadout / state.transport.valueReadout

/-- Both tails and their crossed determinant, with the head denominator
explicit. This formula is not asserted at its zeros. -/
theorem tfvdStateHeadTail_responseDefect {M : ℕ} (z : ℂ)
    (state : CanonicalC3BracketTfvdCompletionState M)
    (hQ : cpChartFactor 3 (operatorHeightParameter z) ≠ 0)
    (hXi : nativeXiCompletionFactor z ≠ 0)
    (hT : state.valueReadout ≠ 0) (hH : state.transport.valueReadout ≠ 0) :
    tfvdStateResponse z state - tfvdStateHeadResponse z state =
      Complex.I * (state.transport.valueReadout * state.logJetTail -
        state.transport.logJetReadout * state.valueTail) /
          (state.transport.valueReadout * (state.transport.valueReadout+state.valueTail)) := by
  rw [tfvdStateResponse_threeChannels z state hQ hXi hT]
  unfold tfvdStateHeadResponse
  have hTT : state.transport.valueReadout+state.valueTail ≠ 0 := hT
  change _ - _ = _
  unfold CanonicalC3BracketTfvdCompletionState.valueReadout
    CanonicalC3BracketTfvdCompletionState.logJetReadout
  field_simp
  ring

def tfvdMaterialSecondCoefficients (N M k : ℕ) (v : Fin N → ℂ)
    (states : Fin N → CanonicalC3BracketTfvdCompletionState M) : Fin N → ℂ :=
  fun j => tfvdStateResponse (canonicalCompletedC3RadialTiltPoint k j) (states j) * v j

def tfvdMaterialWholeSource (N M k : ℕ) (v : Fin N → ℂ)
    (states : Fin N → CanonicalC3BracketTfvdCompletionState M) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  twoPortSynthesis N k v (tfvdMaterialSecondCoefficients N M k v states)

theorem tfvdMaterialWholeSource_canonical (N M k : ℕ) (v : Fin N → ℂ)
    (hstrip : ∀ j : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈
      genuineCriticalStrip)
    (hreg : ∀ j : Fin N,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    tfvdMaterialWholeSource N M k v
      (fun j => canonicalC3BracketTfvdCompletionState M
        (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j))) =
      finiteProjectiveSource N k v := by
  rw [finiteProjectiveSource_eq_twoPorts N k v hreg]
  unfold tfvdMaterialWholeSource tfvdMaterialSecondCoefficients radialResponse
  simp only [tfvdCanonicalResponse_eq_original M _ (hstrip _) (hreg _).1]

/-- Existing value/companion syntheses with c=A*v and literal tilt radius 1.
The enriched TFVD state is the producer of these two readouts. -/
theorem materialSourceChannels_eq_tfvdReadouts (N M k : ℕ) (v : Fin N → ℂ)
    (hstrip : ∀ j : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈
      genuineCriticalStrip) :
    let c := fun j : Fin N => completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k j) * v j
    (sourceValue k c 1, sourceCompanion k c 1) =
      (∑ j, (c j *
          (tfvdStateTracePair (canonicalCompletedC3RadialTiltPoint k j)
            (canonicalC3BracketTfvdCompletionState M
              (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)))).1 /
          completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)) •
            completedNativeRadialChiralCauchyState k j,
       ∑ j, (c j *
          (tfvdStateTracePair (canonicalCompletedC3RadialTiltPoint k j)
            (canonicalC3BracketTfvdCompletionState M
              (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)))).2 /
          completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)) •
            completedNativeRadialChiralCauchyState k j) := by
  dsimp only
  simpa only [Complex.ofReal_one, one_pow, mul_one, tfvdStateTracePair_canonical] using
    source_pair_eq_bracketTfvd M k
      (fun j : Fin N => completedNativeNormalizedPositiveChiralAmplitude
        (canonicalCompletedC3RadialTiltPoint k j) * v j) 1 hstrip

theorem tfvdHeadTail_secondVector (N M k : ℕ) (v : Fin N → ℂ)
    (states : Fin N → CanonicalC3BracketTfvdCompletionState M) :
    tfvdMaterialSecondCoefficients N M k v states -
        (fun j : Fin N => tfvdStateHeadResponse (canonicalCompletedC3RadialTiltPoint k j) (states j) * v j) =
      fun j : Fin N => (tfvdStateResponse (canonicalCompletedC3RadialTiltPoint k j) (states j) -
        tfvdStateHeadResponse (canonicalCompletedC3RadialTiltPoint k j) (states j)) * v j := by
  funext j
  simp only [tfvdMaterialSecondCoefficients, Pi.sub_apply]
  ring

theorem tfvdHeadTail_endpointVector (N M k : ℕ) (v : Fin N → ℂ)
    (states : Fin N → CanonicalC3BracketTfvdCompletionState M) :
    physicalEndpointJetInput N k (tfvdMaterialSecondCoefficients N M k v states) -
      physicalEndpointJetInput N k
        (fun j : Fin N => tfvdStateHeadResponse (canonicalCompletedC3RadialTiltPoint k j) (states j) * v j) =
    physicalEndpointJetInput N k (fun j : Fin N =>
      (tfvdStateResponse (canonicalCompletedC3RadialTiltPoint k j) (states j) -
        tfvdStateHeadResponse (canonicalCompletedC3RadialTiltPoint k j) (states j)) * v j) := by
  rw [← map_sub, tfvdHeadTail_secondVector]

theorem tfvdHeadTail_exactEndpointDefect (N M k : ℕ) (v : Fin N → ℂ)
    (states : Fin N → CanonicalC3BracketTfvdCompletionState M)
    (hQ : ∀ j : Fin N, cpChartFactor 3
      (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)) ≠ 0)
    (hXi : ∀ j : Fin N, nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k j) ≠ 0)
    (hT : ∀ j : Fin N, (states j).valueReadout ≠ 0)
    (hH : ∀ j : Fin N, (states j).transport.valueReadout ≠ 0) :
    physicalEndpointJetInput N k (tfvdMaterialSecondCoefficients N M k v states) -
      physicalEndpointJetInput N k (fun j : Fin N =>
        tfvdStateHeadResponse (canonicalCompletedC3RadialTiltPoint k j) (states j) * v j) =
    physicalEndpointJetInput N k (fun j : Fin N =>
      (Complex.I * ((states j).transport.valueReadout * (states j).logJetTail -
        (states j).transport.logJetReadout * (states j).valueTail) /
          ((states j).transport.valueReadout *
            ((states j).transport.valueReadout+(states j).valueTail))) * v j) := by
  rw [tfvdHeadTail_endpointVector]
  congr 1
  funext j
  rw [tfvdStateHeadTail_responseDefect _ (states j) (hQ j) (hXi j) (hT j) (hH j)]

theorem originalRadialNodes_strip_of_cutoff (N k : ℕ) (hNk : 2*N < k+1) (j : Fin N) :
    operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈ genuineCriticalStrip := by
  have hhalf : (canonicalCompletedC3RadialTiltPoint k j).im < (1/2 : ℝ) := by
    rw [canonicalCompletedC3RadialTiltPoint_im, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    have hNc : (2 : ℝ)*N < k+1 := by exact_mod_cast hNk
    have hj : (j.val : ℝ)+1 ≤ N := by exact_mod_cast j.isLt
    linarith
  have him : 0 < (canonicalCompletedC3RadialTiltPoint k j).im := by
    rw [canonicalCompletedC3RadialTiltPoint_im]
    positivity
  have he : (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)).re =
      1/2 - (canonicalCompletedC3RadialTiltPoint k j).im := by
    norm_num [operatorHeightParameter]
    ring
  constructor <;> rw [he] <;> linarith

theorem materialSourceValue_normalization (N k : ℕ) (v : Fin N → ℂ)
    (hreg : ∀ j : Fin N,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    sourceValue k (fun j : Fin N => completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k j) * v j) 1 =
      portHalfNormalization • radialIncidentSynthesis k N v := by
  unfold sourceValue radialIncidentSynthesis
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Complex.ofReal_one, one_pow, mul_one,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hF := (hreg j).1
  have hP := (hreg j).2
  unfold completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization portHalfNormalization
  field_simp

theorem materialSourceCompanion_normalization (N k : ℕ) (v : Fin N → ℂ)
    (hreg : ∀ j : Fin N,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    sourceCompanion k (fun j : Fin N => completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k j) * v j) 1 =
      portHalfNormalization • radialIncidentSynthesis k N
        (fun j => radialResponse N k j * v j) := by
  unfold sourceCompanion radialIncidentSynthesis
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Complex.ofReal_one, one_pow, mul_one,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hF := (hreg j).1
  have hP := (hreg j).2
  unfold completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization portHalfNormalization radialResponse originalResponse
  field_simp

theorem materialSourceChannels_reconstruct (N k : ℕ) (v : Fin N → ℂ)
    (hP : ∀ j : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    let c := fun j : Fin N => completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k j) * v j
    finiteProjectiveSource N k v =
      (sourceCompanion k c 1 + Complex.I • sourceValue k c 1,
       sourceCompanion k c 1 - Complex.I • sourceValue k c 1) := by
  dsimp only
  apply Prod.ext
  · have he := incident_synthesis_eq_source k
      (fun j : Fin N => completedNativeNormalizedPositiveChiralAmplitude
        (canonicalCompletedC3RadialTiltPoint k j) * v j) 1 hP
    simpa only [Complex.ofReal_one, one_pow, mul_one, finiteProjectiveSource, Prod.fst_sum,
      canonicalCompletedNativeRadialProjectiveChiralState, canonicalCompletedNativeRadialChiralDefectState,
      Prod.smul_fst, smul_smul, mul_comm] using he
  · have he := returned_synthesis_eq_source k
      (fun j : Fin N => completedNativeNormalizedPositiveChiralAmplitude
        (canonicalCompletedC3RadialTiltPoint k j) * v j) 1 hP
    simpa only [Complex.ofReal_one, one_pow, mul_one, finiteProjectiveSource, Prod.snd_sum,
      canonicalCompletedNativeRadialProjectiveChiralState, canonicalCompletedNativeRadialChiralDefectState,
      Prod.smul_snd, smul_smul, mul_comm] using he

theorem tfvdCanonicalSecondPort_endpointCompletion (N M k : ℕ) (v : Fin N → ℂ)
    (hstrip : ∀ j : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈
      genuineCriticalStrip)
    (hF : ∀ j : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    physicalEndpointJetInput N k
      (tfvdMaterialSecondCoefficients N M k v
        (fun j : Fin N => canonicalC3BracketTfvdCompletionState M
          (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)))) =
      endpointCompletion N k (fun j : ℕ => originalResponse (canonicalCompletedC3RadialTiltPoint k j))
        (physicalEndpointJetInput N k v) := by
  have he : tfvdMaterialSecondCoefficients N M k v
      (fun j : Fin N => canonicalC3BracketTfvdCompletionState M
        (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j))) =
      fun j : Fin N => originalResponse (canonicalCompletedC3RadialTiltPoint k j) * v j := by
    funext j
    change tfvdStateResponse (canonicalCompletedC3RadialTiltPoint k j)
      (canonicalC3BracketTfvdCompletionState M
        (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j))) * v j = _
    rw [tfvdCanonicalResponse_eq_original M _ (hstrip j) (hF j)]
  rw [he]
  exact physicalEndpointJetInput_completion N k
    (fun j : ℕ => originalResponse (canonicalCompletedC3RadialTiltPoint k j)) v

end
end CarrySelfAdjointOperator.PhysicalSewing

import CarrySelfAdjointOperator.CompletedNativeC2ExactTailTransport

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open CarrySelfAdjointOperator.ChiralReturn

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-! ## Scalar relative logarithmic response -/

/-- The logarithmic response `-f'/(2f)` of a scalar characteristic. -/
def c2LogarithmicResponse (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  -deriv f z / (2 * f z)

/-- Cleared-denominator form of the relative response identity. -/
theorem c2RelativeResponse_cleared_identity
    (h t hp tp : ℂ) :
    -(hp + tp) * h + hp * (h + t) = -(h * tp - hp * t) := by
  ring

/-- Algebraic relative response identity. The two denominators are kept
explicit so callers provide exactly the nonvanishing they need. -/
theorem c2RelativeResponse_scalar_identity
    (h t hp tp : ℂ) (hh : h ≠ 0) (hht : h + t ≠ 0) :
    -(hp + tp) / (2 * (h + t)) + hp / (2 * h) =
      -(h * tp - hp * t) / (2 * h * (h + t)) := by
  field_simp [hh, hht]
  ring

/-- HasDerivAt form of the head-tail logarithmic response identity. -/
theorem c2LogarithmicResponse_addTail_eq_wronskian
    (h t : ℂ → ℂ) (z hp tp : ℂ)
    (hh : HasDerivAt h hp z) (ht : HasDerivAt t tp z)
    (hnz : h z ≠ 0) (hsum : h z + t z ≠ 0) :
    c2LogarithmicResponse (fun w => h w + t w) z -
        c2LogarithmicResponse h z =
      -(h z * tp - hp * t z) /
        (2 * h z * (h z + t z)) := by
  unfold c2LogarithmicResponse
  have hsumDeriv : HasDerivAt (fun w => h w + t w) (hp + tp) z :=
    (hh.add ht).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  rw [hsumDeriv.deriv, hh.deriv]
  calc
    _ = -(hp + tp) / (2 * (h z + t z)) + hp / (2 * h z) := by ring
    _ = _ := c2RelativeResponse_scalar_identity
      (h z) (t z) hp tp hnz hsum

/-- Relative response as the logarithmic derivative of the relative tail. -/
theorem c2LogarithmicResponse_addTail_eq_relative_deriv
    (h t : ℂ → ℂ) (z hp tp : ℂ)
    (hh : HasDerivAt h hp z) (ht : HasDerivAt t tp z)
    (hnz : h z ≠ 0) (hsum : h z + t z ≠ 0) :
    c2LogarithmicResponse (fun w => h w + t w) z -
        c2LogarithmicResponse h z =
      -deriv (fun w => t w / h w) z /
        (2 * (1 + t z / h z)) := by
  have hratio : 1 + t z / h z = (h z + t z) / h z := by
    field_simp [hnz]
  have hquot : HasDerivAt (fun w => t w / h w)
      ((tp * h z - t z * hp) / h z ^ 2) z :=
    (ht.div hh hnz).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  rw [c2LogarithmicResponse_addTail_eq_wronskian h t z hp tp hh ht hnz hsum]
  rw [hquot.deriv, hratio]
  field_simp [hnz, hsum]

/-- Multiplication by a common differentiable dressing contributes no term
to the head-tail Wronskian. -/
theorem c2ProductWronskian_cancel_dressing
    (L V T : ℂ → ℂ) (z L' V' T' : ℂ)
    (hL : HasDerivAt L L' z) (hV : HasDerivAt V V' z)
    (hT : HasDerivAt T T' z) :
    (L z * V z) * deriv (fun w => L w * T w) z -
        deriv (fun w => L w * V w) z * (L z * T z) =
      (L z) ^ 2 * (V z * T' - V' * T z) := by
  have hLT : HasDerivAt (fun w => L w * T w)
      (L' * T z + L z * T') z :=
    (hL.mul hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hLV : HasDerivAt (fun w => L w * V w)
      (L' * V z + L z * V') z :=
    (hL.mul hV).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  rw [hLT.deriv, hLV.deriv]
  ring

/-- The logarithmic-response error for a head and tail with the same
differentiable dressing is independent of that dressing. -/
theorem c2LogarithmicResponse_cancel_commonDressing
    (L V T : ℂ → ℂ) (z L' V' T' : ℂ)
    (hL : HasDerivAt L L' z) (hV : HasDerivAt V V' z)
    (hT : HasDerivAt T T' z)
    (hL0 : L z ≠ 0) (hV0 : V z ≠ 0)
    (hVT0 : V z + T z ≠ 0) :
    c2LogarithmicResponse (fun w => L w * (V w + T w)) z -
        c2LogarithmicResponse (fun w => L w * V w) z =
      c2LogarithmicResponse (fun w => V w + T w) z -
        c2LogarithmicResponse V z := by
  let H : ℂ → ℂ := fun w => L w * V w
  let Tail : ℂ → ℂ := fun w => L w * T w
  let hp := L' * V z + L z * V'
  let tp := L' * T z + L z * T'
  have hH : HasDerivAt H hp z := by
    change HasDerivAt (fun w => L w * V w) _ z
    exact (hL.mul hV).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hTail : HasDerivAt Tail tp z := by
    change HasDerivAt (fun w => L w * T w) _ z
    exact (hL.mul hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hsumNZ : L z * V z + L z * T z ≠ 0 := by
    have hprod := mul_ne_zero hL0 hVT0
    simpa [mul_add] using hprod
  have hresponseLocal :
      c2LogarithmicResponse (fun w => L w * (V w + T w)) z =
        c2LogarithmicResponse (fun w => H w + Tail w) z := by
    have hlocal : (fun w => L w * (V w + T w)) =ᶠ[nhds z]
        (fun w => H w + Tail w) :=
      Filter.Eventually.of_forall fun w => by simp [H, Tail, mul_add]
    unfold c2LogarithmicResponse
    rw [hlocal.deriv_eq, hlocal.self_of_nhds]
  have hleft := c2LogarithmicResponse_addTail_eq_wronskian
    H Tail z hp tp hH hTail
    (mul_ne_zero hL0 hV0)
    (by simpa [H, Tail] using hsumNZ)
  have hright := c2LogarithmicResponse_addTail_eq_wronskian
    V T z V' T' hV hT hV0 hVT0
  have hDress := c2ProductWronskian_cancel_dressing
    L V T z L' V' T' hL hV hT
  have hDress' : H z * tp - hp * Tail z =
      L z ^ 2 * (V z * T' - V' * T z) := by
    calc
      H z * tp - hp * Tail z =
          H z * deriv Tail z - deriv H z * Tail z := by
            rw [← hTail.deriv, ← hH.deriv]
      _ = _ := by simpa [H, Tail] using hDress
  rw [hresponseLocal, hleft, hDress', hright]
  simp only [H, Tail]
  field_simp [hL0, hV0, hVT0, hsumNZ]

/-- A constant multiple of the head has zero relative response correction. -/
theorem c2LogarithmicResponse_addTail_eq_zero_of_proportional
    (h t : ℂ → ℂ) (z hp : ℂ) (a : ℂ)
    (hh : HasDerivAt h hp z) (ht : HasDerivAt t (deriv t z) z)
    (hnz : h z ≠ 0) (hsum : h z + t z ≠ 0)
    (hprop : ∀ w, t w = a * h w) :
    c2LogarithmicResponse (fun w => h w + t w) z -
        c2LogarithmicResponse h z = 0 := by
  have hlocal : t =ᶠ[nhds z] (fun w => a * h w) :=
    Filter.Eventually.of_forall hprop
  have htp : deriv t z = a * hp := by
    rw [hlocal.deriv_eq, (hh.const_mul a).deriv]
  rw [c2LogarithmicResponse_addTail_eq_wronskian h t z hp (deriv t z)
    hh ht hnz hsum]
  rw [hprop z, htp]
  ring

/-! ## Exact C2 source Wronskian -/

/-- The completion-dressed exact tail on the original spectral height line. -/
def nativeC2ExactTailHeightCompletion (M : ℕ) (z : ℂ) : ℂ :=
  c2CompletionDressing z *
    nativeC2ExactCenterTail M (c2SpectralLine z)

/-- Relative C2 Wronskian in the original exponent variable. The finite chart
includes its original seed, which remains in both the numerator and
denominator. -/
def nativeC2ExactTailRelativeWronskian (M : ℕ) (z : ℂ) : ℂ :=
  let V := c2FiniteChartHeightValue M z
  let J := c2FiniteChartHeightJet M z
  let T := nativeC2ExactCenterTail M (c2SpectralLine z)
  let JT := -deriv (nativeC2ExactCenterTail M) (c2SpectralLine z)
  (V * JT - J * T) / (V * (V + T))

/-- The existing finite C2 cell identity expands the jet contribution into
the central term and both independent leg corrections. -/
theorem nativeC2ExactTailRelativeWronskian_eq_central_legs
    (M : ℕ) (z : ℂ) :
    nativeC2ExactTailRelativeWronskian M z =
      (c2FiniteChartHeightValue M z *
          (-deriv (nativeC2ExactCenterTail M) (c2SpectralLine z)) -
        c2FiniteChartHeightCentral M z *
          nativeC2ExactCenterTail M (c2SpectralLine z) -
        c2FiniteChartHeightLegCorrection M z *
          nativeC2ExactCenterTail M (c2SpectralLine z)) /
        (c2FiniteChartHeightValue M z *
          (c2FiniteChartHeightValue M z +
            nativeC2ExactCenterTail M (c2SpectralLine z))) := by
  let V := c2FiniteChartHeightValue M z
  let J := c2FiniteChartHeightJet M z
  let T := nativeC2ExactCenterTail M (c2SpectralLine z)
  let JT := -deriv (nativeC2ExactCenterTail M) (c2SpectralLine z)
  have hJet : J = c2FiniteChartHeightCentral M z +
      c2FiniteChartHeightLegCorrection M z := by
    simpa [J, c2FiniteChartHeightJet, c2FiniteChartHeightCentral,
      c2FiniteChartHeightLegCorrection] using
      c2FiniteChartJet_eq_central_add_legCorrection M (c2SpectralLine z)
  change (V * JT - J * T) / (V * (V + T)) = _
  rw [hJet]
  apply congrArg (fun q : ℂ => q / (V * (V + T)))
  ring

/-- Algebraic cancellation of the common dressing after the height-line
derivatives have contributed their factors of `i`. -/
theorem c2RelativeResponse_dressing_algebra
    (l v u j jt : ℂ) (hl : l ≠ 0) (hv : v ≠ 0)
    (hvu : v + u ≠ 0) :
    -(l ^ 2 * (v * (-Complex.I * jt) -
        (-Complex.I * j) * u)) /
        (2 * (l * v) * (l * v + l * u)) =
      Complex.I * ((v * jt - j * u) / (v * (v + u))) / 2 := by
  field_simp [hl, hv, hvu]
  ring

/-- Exact C2 relative response identity. The completed and finite
characteristics retain their full dressing; the hypotheses name their exact
nonvanishing conditions. -/
theorem completedNativeC2_relativeLogarithmicResponse_eq_i_mul_exactTailWronskian
    (M : ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hHead : c2FiniteChartHeightCharacteristic M z ≠ 0)
    (hFull : completedNativeOperatorCharacteristic z ≠ 0) :
    c2LogarithmicResponse completedNativeOperatorCharacteristic z -
        c2LogarithmicResponse (c2FiniteChartHeightCharacteristic M) z =
      Complex.I * nativeC2ExactTailRelativeWronskian M z / 2 := by
  let V : ℂ → ℂ := fun w => c2FiniteChartHeightValue M w
  let U : ℂ → ℂ := fun w =>
    nativeC2ExactCenterTail M (c2SpectralLine w)
  let L : ℂ → ℂ := c2CompletionDressing
  let H : ℂ → ℂ := fun w => L w * V w
  let T : ℂ → ℂ := fun w => L w * U w
  have hsDomain : z ∈ completedNativeHeightDomain := by
    simpa [completedNativeHeightDomain] using hs
  have hlocal : completedNativeOperatorCharacteristic =ᶠ[nhds z]
      (fun w => H w + T w) := by
    filter_upwards [isOpen_completedNativeHeightDomain.mem_nhds hsDomain]
      with w hw
    have hscalar := completedNativeC2Characteristic_sub_finite_eq_completion_mul_exactTail
      M w (by simpa [completedNativeHeightDomain] using hw)
    rw [← c2SpectralLine_eq_operatorHeightParameter w] at hscalar
    have hscalar' : completedNativeOperatorCharacteristic w -
        L w * V w = L w * U w := by
      simpa [c2FiniteChartHeightCharacteristic, c2ProductCharacteristic,
        L, V, U] using hscalar
    have hsum : completedNativeOperatorCharacteristic w = H w + T w := by
      calc
        completedNativeOperatorCharacteristic w =
            (completedNativeOperatorCharacteristic w - H w) + H w := by ring
        _ = _ := by
          change completedNativeOperatorCharacteristic w -
              L w * V w + L w * V w = L w * V w + L w * U w
          rw [hscalar']
          ring
    exact hsum
  have hpoint : completedNativeOperatorCharacteristic z = H z + T z :=
    hlocal.self_of_nhds
  have hL := c2CompletionDressing_hasDerivAt z hs
  have hV : HasDerivAt V
      (-Complex.I * c2FiniteChartHeightJet M z) z := by
    change HasDerivAt
      (fun w => c2FiniteChartValue M (c2SpectralLine w)) _ z
    exact c2FiniteChartValue_hasDerivAt_spectralLine M z
  have hU : HasDerivAt U
      (Complex.I * deriv (nativeC2ExactCenterTail M)
        (c2SpectralLine z)) z := by
    simpa [U] using nativeC2ExactCenterTailHeight_hasDerivAt M z hs
  let hp := c2CompletionDressingDerivative z * V z +
    L z * (-Complex.I * c2FiniteChartHeightJet M z)
  let tp := c2CompletionDressingDerivative z * U z +
    L z * (Complex.I * deriv (nativeC2ExactCenterTail M)
      (c2SpectralLine z))
  have hH : HasDerivAt H hp z := by
    change HasDerivAt (fun w => L w * V w) _ z
    exact (hL.mul hV).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hT : HasDerivAt T tp z := by
    change HasDerivAt (fun w => L w * U w) _ z
    exact (hL.mul hU).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hH_eq : H = c2FiniteChartHeightCharacteristic M := by
    funext w
    rfl
  have hH0 : H z ≠ 0 := by
    simpa [H, L, V, c2FiniteChartHeightCharacteristic,
      c2ProductCharacteristic] using hHead
  have hL0 : L z ≠ 0 := by
    intro hzero
    apply hH0
    simp [H, L, V, hzero]
  have hV0 : V z ≠ 0 := by
    intro hzero
    apply hH0
    simp [H, L, V, hzero]
  have hsum0 : H z + T z ≠ 0 := by
    rw [← hpoint]
    exact hFull
  have hrelative := c2LogarithmicResponse_addTail_eq_wronskian
    H T z hp tp hH hT hH0 hsum0
  have hresponse :
      c2LogarithmicResponse completedNativeOperatorCharacteristic z -
        c2LogarithmicResponse (c2FiniteChartHeightCharacteristic M) z =
      c2LogarithmicResponse (fun w => H w + T w) z -
        c2LogarithmicResponse H z := by
    unfold c2LogarithmicResponse
    rw [hlocal.deriv_eq, hpoint, hH_eq]
  have hcancel := c2ProductWronskian_cancel_dressing L V U z
    (c2CompletionDressingDerivative z)
    (-Complex.I * c2FiniteChartHeightJet M z)
    (Complex.I * deriv (nativeC2ExactCenterTail M)
      (c2SpectralLine z)) hL hV hU
  have hcancel' :
      (H z) * tp - hp * T z =
        (L z) ^ 2 *
          (V z * (Complex.I * deriv (nativeC2ExactCenterTail M)
                (c2SpectralLine z)) -
            (-Complex.I * c2FiniteChartHeightJet M z) * U z) := by
    calc
      (H z) * tp - hp * T z =
          H z * deriv T z - deriv H z * T z := by
            rw [← hT.deriv, ← hH.deriv]
      _ = _ := by
        simpa [H, T, L, V, U] using hcancel
  have hsumL : L z * (V z + U z) ≠ 0 := by
    intro hz
    apply hFull
    calc
      completedNativeOperatorCharacteristic z = H z + T z := hpoint
      _ = L z * (V z + U z) := by
        dsimp [H, T, L, V, U]
        ring
      _ = 0 := by simp [hz]
  have hVU0 : V z + U z ≠ 0 := by
    intro hu
    apply hsumL
    simp [hu]
  have hHval : H z = L z * V z := rfl
  have hTval : T z = L z * U z := rfl
  have hUderiv :
      Complex.I * deriv (nativeC2ExactCenterTail M)
          (c2SpectralLine z) =
        -Complex.I *
          (-deriv (nativeC2ExactCenterTail M)
            (c2SpectralLine z)) := by ring
  rw [hresponse, hrelative, hcancel', hHval, hTval, hUderiv]
  unfold nativeC2ExactTailRelativeWronskian
  dsimp [V, U]
  exact c2RelativeResponse_dressing_algebra
    (L z) (V z) (nativeC2ExactCenterTail M (c2SpectralLine z))
    (c2FiniteChartHeightJet M z)
    (-deriv (nativeC2ExactCenterTail M) (c2SpectralLine z))
    hL0 hV0
    hVU0

/-! ## Signed Hilbert crossings -/

/-- Signed chiral crossing in the original complex Hilbert space. -/
def c2SignedCrossing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (V C : E) : ℝ :=
  ‖C + Complex.I • V‖ ^ 2 - ‖C - Complex.I • V‖ ^ 2

/-- Existing chiral orientation: the first inner-product argument is
conjugate-linear, giving `+4 Im ⟪V,C⟫`. -/
theorem c2SignedCrossing_eq_four_im_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V C : E) :
    c2SignedCrossing V C = 4 * (inner ℂ V C).im := by
  exact norm_chiral_balance_eq_source_cross V C

/-- Adding an imaginary leg to the companion transports the signed crossing
by `4 Re ⟪V,E⟫`. -/
theorem c2SignedCrossing_add_imaginary_leg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V C E₀ : E) :
    c2SignedCrossing V (C + Complex.I • E₀) - c2SignedCrossing V C =
      4 * (inner ℂ V E₀).re := by
  rw [c2SignedCrossing_eq_four_im_inner,
    c2SignedCrossing_eq_four_im_inner, inner_add_right, inner_smul_right,
    Complex.add_im, Complex.I_mul_im]
  ring

/-- Exact two-sided first variation of the signed crossing. -/
theorem c2SignedCrossing_joint_variation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V C dV dC : E) :
    c2SignedCrossing (V + dV) (C + dC) - c2SignedCrossing V C =
      4 * (inner ℂ V dC + inner ℂ dV C + inner ℂ dV dC).im := by
  rw [c2SignedCrossing_eq_four_im_inner,
    c2SignedCrossing_eq_four_im_inner, inner_add_left, inner_add_right,
    inner_add_right]
  simp only [Complex.add_im]
  ring

/-- The existing finite C2 companion decomposition transports its two
independent legs into the signed crossing in the unchanged source carrier. -/
theorem nativeSourceC2Approx_signed_leg_crossing
    (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    c2SignedCrossing (nativeSourceC2ApproxValue n k M x)
        (nativeSourceC2ApproxCompanion n k M x) -
      c2SignedCrossing (nativeSourceC2ApproxValue n k M x)
        (nativeSourceC2ApproxCentral n k M x) =
      4 * (inner ℂ (nativeSourceC2ApproxValue n k M x)
        (nativeSourceC2ApproxLegs n k M x)).re := by
  rw [nativeSourceC2ApproxCompanion_eq_central_add_legs]
  exact c2SignedCrossing_add_imaginary_leg _ _ _

/-- The complete signed source crossing varies by the exact value and
companion tail vectors already defined with the full Hermite--Biehler weights. -/
theorem nativeSourceC2_signed_tail_crossing_variation
    (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    c2SignedCrossing
        (sourceValue k (nativeSourceChiralJetInput n k x) 1)
        (sourceCompanion k (nativeSourceChiralJetInput n k x) 1) -
      c2SignedCrossing (nativeSourceC2ApproxValue n k M x)
        (nativeSourceC2ApproxCompanion n k M x) =
      4 * (inner ℂ (nativeSourceC2ApproxValue n k M x)
            (nativeSourceC2CompanionTail n k M x) +
          inner ℂ (nativeSourceC2ValueTail n k M x)
            (nativeSourceC2ApproxCompanion n k M x) +
          inner ℂ (nativeSourceC2ValueTail n k M x)
            (nativeSourceC2CompanionTail n k M x)).im := by
  have hV : sourceValue k (nativeSourceChiralJetInput n k x) 1 =
      nativeSourceC2ApproxValue n k M x + nativeSourceC2ValueTail n k M x := by
    unfold nativeSourceC2ValueTail
    abel
  have hC : sourceCompanion k (nativeSourceChiralJetInput n k x) 1 =
      nativeSourceC2ApproxCompanion n k M x +
        nativeSourceC2CompanionTail n k M x := by
    unfold nativeSourceC2CompanionTail
    abel
  rw [hV, hC]
  exact c2SignedCrossing_joint_variation _ _ _ _

/-- The scalar exact-tail identity has a vector adapter in the original C2
source carrier; the complete Hermite--Biehler denominators and radial states
are inherited from the existing source weight and synthesis. -/
theorem nativeSourceC2_valueTail_eq_originalExactCenterTailSynthesis
    (n k M : ℕ) (x : Fin (2*n) → ℂ)
    (hstrip : ∀ i : Fin (2*n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    nativeSourceC2ValueTail n k M x =
      nativeSourceC2ExactValueTailSynthesis n k M x :=
  nativeSourceC2ValueTail_eq_exactCenterTailSynthesis n k M x hstrip

/-- The exact companion-tail adapter uses the expanded differentiated tail,
including the derivative of the original dressing and the chain factor `i`. -/
theorem nativeSourceC2_companionTail_eq_originalExactCenterTailSynthesis
    (n k M : ℕ) (x : Fin (2*n) → ℂ)
    (hstrip : ∀ i : Fin (2*n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    nativeSourceC2CompanionTail n k M x =
      nativeSourceC2ExactCompanionTailSynthesis n k M x :=
  nativeSourceC2CompanionTail_eq_exactCenterTailSynthesis n k M x hstrip

end
end CarrySelfAdjointOperator

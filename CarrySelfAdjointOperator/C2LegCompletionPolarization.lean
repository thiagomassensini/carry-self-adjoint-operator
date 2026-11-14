import CarrySelfAdjointOperator.C2LegJetCompensation
import CarrySelfAdjointOperator.NativeBoundaryArchimedeanDressingSeparation

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge

noncomputable section

/-- The height parameter used by the C2 camera. -/
def c2SpectralLine (z : ℂ) : ℂ := (1 / 2 : ℂ) + z * Complex.I

/-- The multiplicative C2 dressing, with the original completion and camera
factor kept visible. -/
def c2CompletionDressing (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z / factor 2 (c2SpectralLine z)

/-- Product characteristic associated with a dressing and a source chart. -/
def c2ProductCharacteristic (L V : ℂ → ℂ) (z : ℂ) : ℂ :=
  L z * V z

/-- Companions assembled from the logarithmic jet and the dressing derivative. -/
def c2CompletedCompanion (L L' V J : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * L z * J z - L' z * V z

/-- The same companion with the central logarithmic bracket in place of the
full two-leg jet. -/
def c2CentralCompanion (L L' V d : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * L z * d z - L' z * V z

/-- The aligned C2 fibre centre corresponding to one original stencil cell. -/
def c2FiniteChartCenter (index : ℕ) : ℝ :=
  ((2 ^ c2AlignedIndexDepth index * c2AlignedIndexCore index : ℕ) : ℝ)

/-- The finite C2 value chart. Its constant seed is retained as part of `V`. -/
def c2FiniteChartValue (cutoff : ℕ) (s : ℂ) : ℂ :=
  1 + ∑ index ∈ Finset.range cutoff,
    c2LegJetBracket 0 s (c2FiniteChartCenter index)

/-- The all-cell first logarithmic jet of the finite C2 chart. -/
def c2FiniteChartJet (cutoff : ℕ) (s : ℂ) : ℂ :=
  ∑ index ∈ Finset.range cutoff,
    c2LegJetBracket 1 s (c2FiniteChartCenter index)

/-- The sum of the central logarithmic brackets. -/
def c2FiniteChartCentral (cutoff : ℕ) (s : ℂ) : ℂ :=
  ∑ index ∈ Finset.range cutoff,
    c2LegCentralPart 1 s (c2FiniteChartCenter index)

/-- The two-leg source correction, summed over the original finite C2 cut. -/
def c2FiniteChartLegCorrection (cutoff : ℕ) (s : ℂ) : ℂ :=
  ∑ index ∈ Finset.range cutoff,
    c2LegCompensation 1 s (c2FiniteChartCenter index)

/-- The finite C2 chart satisfies `J = d + E` cell by cell. -/
theorem c2FiniteChartJet_eq_central_add_legCorrection
    (cutoff : ℕ) (s : ℂ) :
    c2FiniteChartJet cutoff s =
      c2FiniteChartCentral cutoff s +
        c2FiniteChartLegCorrection cutoff s := by
  unfold c2FiniteChartJet c2FiniteChartCentral c2FiniteChartLegCorrection
  calc
    (∑ index ∈ Finset.range cutoff,
        c2LegJetBracket 1 s (c2FiniteChartCenter index)) =
      ∑ index ∈ Finset.range cutoff,
        (c2LegCentralPart 1 s (c2FiniteChartCenter index) +
          c2LegCompensation 1 s (c2FiniteChartCenter index)) := by
        apply Finset.sum_congr rfl
        intro index _
        exact c2LegJetBracket_eq_central_add_compensation 1 s
          (c2FiniteChartCenter index)
    _ = (∑ index ∈ Finset.range cutoff,
          c2LegCentralPart 1 s (c2FiniteChartCenter index)) +
        ∑ index ∈ Finset.range cutoff,
          c2LegCompensation 1 s (c2FiniteChartCenter index) := by
        rw [Finset.sum_add_distrib]

/-- Derivative of the height-line parameter. -/
theorem hasDerivAt_c2SpectralLine (z : ℂ) :
    HasDerivAt c2SpectralLine Complex.I z := by
  refine ((((hasDerivAt_const (x := z) (c := (1 / 2 : ℂ))).add
    ((hasDerivAt_id z).mul_const Complex.I)).congr_of_eventuallyEq ?_).congr_deriv ?_)
  · exact Filter.Eventually.of_forall (fun w => by simp [c2SpectralLine])
  · ring

/-- One leg sample differentiated along `s(z)=1/2+iz`. -/
theorem hasDerivAt_c2LegFunction_spectralLine
    (x : ℝ) (z : ℂ) :
    HasDerivAt (fun w => c2LegFunction (c2SpectralLine w) x)
      (-Complex.I * (Real.log x : ℂ) *
        c2LegFunction (c2SpectralLine z) x) z := by
  have harg : HasDerivAt
      (fun w => -c2SpectralLine w * (Real.log x : ℂ))
      (-Complex.I * (Real.log x : ℂ)) z := by
    exact (hasDerivAt_c2SpectralLine z).neg.mul_const
      (Real.log x : ℂ)
  have hexp := harg.cexp
  change HasDerivAt
    (fun w => Complex.exp (-c2SpectralLine w * (Real.log x : ℂ)))
    (-Complex.I * (Real.log x : ℂ) *
      Complex.exp (-c2SpectralLine z * (Real.log x : ℂ))) z
  exact hexp.congr_deriv (by ring)

/-- Exponent derivative of one literal C2 leg sample. -/
theorem hasDerivAt_c2LegFunction_exponent
    (x : ℝ) (s : ℂ) :
    HasDerivAt (fun u => c2LegFunction u x)
      (-(Real.log x : ℂ) * c2LegFunction s x) s := by
  have harg : HasDerivAt
      (fun u => -u * (Real.log x : ℂ))
      (-(Real.log x : ℂ)) s := by
    refine (((hasDerivAt_id s).neg.mul_const
      (Real.log x : ℂ)).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun u => by
        dsimp)
    · ring
  have hexp := harg.cexp
  change HasDerivAt
    (fun u => Complex.exp (-u * (Real.log x : ℂ)))
    (-(Real.log x : ℂ) *
      Complex.exp (-s * (Real.log x : ℂ))) s
  exact hexp.congr_deriv (by ring)

/-- Each logarithmic bracket jet differentiates to the next jet on the height
line. -/
theorem c2LegJetBracket_hasDerivAt_spectralLine
    (order : ℕ) (center : ℝ) (z : ℂ) :
    HasDerivAt (fun w =>
      c2LegJetBracket order (c2SpectralLine w) center)
      (-Complex.I * c2LegJetBracket (order + 1)
        (c2SpectralLine z) center) z := by
  have hleft := hasDerivAt_c2LegFunction_spectralLine (center - 1) z
  have hmid := hasDerivAt_c2LegFunction_spectralLine center z
  have hright := hasDerivAt_c2LegFunction_spectralLine (center + 1) z
  have hleft' : HasDerivAt
      (fun w => c2LegLogWeight order (center - 1) *
        c2LegFunction (c2SpectralLine w) (center - 1))
      (c2LegLogWeight order (center - 1) *
        (-Complex.I * (Real.log (center - 1) : ℂ) *
          c2LegFunction (c2SpectralLine z) (center - 1))) z :=
    hleft.const_mul (c2LegLogWeight order (center - 1))
  have hmid' : HasDerivAt
      (fun w => c2LegLogWeight order center *
        c2LegFunction (c2SpectralLine w) center)
      (c2LegLogWeight order center *
        (-Complex.I * (Real.log center : ℂ) *
          c2LegFunction (c2SpectralLine z) center)) z :=
    hmid.const_mul (c2LegLogWeight order center)
  have hright' : HasDerivAt
      (fun w => c2LegLogWeight order (center + 1) *
        c2LegFunction (c2SpectralLine w) (center + 1))
      (c2LegLogWeight order (center + 1) *
        (-Complex.I * (Real.log (center + 1) : ℂ) *
          c2LegFunction (c2SpectralLine z) (center + 1))) z :=
    hright.const_mul (c2LegLogWeight order (center + 1))
  have hbracket := (hleft'.sub (hmid'.const_mul 2)).add hright'
  refine hbracket.congr_deriv ?_
  simp only [c2LegJetBracket, c2LegJetValue, c2LegLogWeight]
  rw [pow_succ]
  ring

/-- Exponent differentiation of each logarithmic bracket raises the jet
order by one and contributes the expected minus sign. -/
theorem c2LegJetBracket_hasDerivAt_exponent
    (order : ℕ) (center : ℝ) (s : ℂ) :
    HasDerivAt (fun u => c2LegJetBracket order u center)
      (-c2LegJetBracket (order + 1) s center) s := by
  have hleft := hasDerivAt_c2LegFunction_exponent (center - 1) s
  have hmid := hasDerivAt_c2LegFunction_exponent center s
  have hright := hasDerivAt_c2LegFunction_exponent (center + 1) s
  have hleft' : HasDerivAt
      (fun u => c2LegLogWeight order (center - 1) *
        c2LegFunction u (center - 1))
      (c2LegLogWeight order (center - 1) *
        (-(Real.log (center - 1) : ℂ) *
          c2LegFunction s (center - 1))) s :=
    hleft.const_mul (c2LegLogWeight order (center - 1))
  have hmid' : HasDerivAt
      (fun u => c2LegLogWeight order center * c2LegFunction u center)
      (c2LegLogWeight order center *
        (-(Real.log center : ℂ) * c2LegFunction s center)) s :=
    hmid.const_mul (c2LegLogWeight order center)
  have hright' : HasDerivAt
      (fun u => c2LegLogWeight order (center + 1) *
        c2LegFunction u (center + 1))
      (c2LegLogWeight order (center + 1) *
        (-(Real.log (center + 1) : ℂ) *
          c2LegFunction s (center + 1))) s :=
    hright.const_mul (c2LegLogWeight order (center + 1))
  have hbracket := (hleft'.sub (hmid'.const_mul 2)).add hright'
  refine hbracket.congr_deriv ?_
  simp only [c2LegJetBracket, c2LegJetValue, c2LegLogWeight]
  rw [pow_succ]
  ring

/-- The finite C2 chart has source derivative `-iJ`. -/
theorem c2FiniteChartValue_hasDerivAt_spectralLine
    (cutoff : ℕ) (z : ℂ) :
    HasDerivAt (fun w => c2FiniteChartValue cutoff (c2SpectralLine w))
      (-Complex.I * c2FiniteChartJet cutoff (c2SpectralLine z)) z := by
  have hsum : HasDerivAt
      (fun w => ∑ index ∈ Finset.range cutoff,
        c2LegJetBracket 0 (c2SpectralLine w) (c2FiniteChartCenter index))
      (∑ index ∈ Finset.range cutoff,
        -Complex.I * c2LegJetBracket 1
          (c2SpectralLine z) (c2FiniteChartCenter index)) z :=
    HasDerivAt.fun_sum fun index _ =>
      c2LegJetBracket_hasDerivAt_spectralLine 0
        (c2FiniteChartCenter index) z
  have hwhole := (hasDerivAt_const z (1 : ℂ)).add hsum
  refine (hwhole.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun w => by
      simp [c2FiniteChartValue])
  · simp [c2FiniteChartJet, Finset.mul_sum]

/-- The seed is retained in the value chart, and its exponent derivative
vanishes. The finite C2 chart therefore satisfies exactly dV/ds = -J. -/
theorem c2FiniteChartValue_hasDerivAt_exponent
    (cutoff : ℕ) (s : ℂ) :
    HasDerivAt (c2FiniteChartValue cutoff)
      (-c2FiniteChartJet cutoff s) s := by
  have hsum : HasDerivAt
      (fun u => ∑ index ∈ Finset.range cutoff,
        c2LegJetBracket 0 u (c2FiniteChartCenter index))
      (∑ index ∈ Finset.range cutoff,
        -c2LegJetBracket 1 s (c2FiniteChartCenter index)) s :=
    HasDerivAt.fun_sum fun index _ =>
      c2LegJetBracket_hasDerivAt_exponent 0
        (c2FiniteChartCenter index) s
  have hwhole := (hasDerivAt_const s (1 : ℂ)).add hsum
  refine (hwhole.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun u => by
      simp [c2FiniteChartValue])
  · simp [c2FiniteChartJet]

/-- A finite fibre stencil is the logarithmic-order-zero jet on its three
positive samples. -/
theorem c2FiniteFiberStencilBracket_eq_legJet
    (s : ℂ) (m k : ℕ) (hcenter : 1 < 2 ^ k * m) :
    evalFormalStencil (fun n => realDirichletPower s (n : ℝ))
        (centeredBracketStencil (2 ^ k * m) 1) =
      c2LegJetBracket 0 s (((2 ^ k * m : ℕ) : ℝ)) := by
  have hcenter_le : 1 ≤ 2 ^ k * m := hcenter.le
  have hleft_cast : (((2 ^ k * m - 1 : ℕ) : ℝ)) =
      ((2 ^ k * m : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hcenter_le]
    norm_num
  have hright_cast : (((2 ^ k * m + 1 : ℕ) : ℝ)) =
      ((2 ^ k * m : ℕ) : ℝ) + 1 := by
    norm_num
  have hleft_pos : 0 < (((2 ^ k * m - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt hcenter
  have hleft_argument_pos :
      0 < (((2 ^ k * m : ℕ) : ℝ) - 1) := by
    rw [← hleft_cast]
    exact hleft_pos
  have hcenter_pos : 0 < (((2 ^ k * m : ℕ) : ℝ)) := by positivity
  have hright_pos : 0 < (((2 ^ k * m + 1 : ℕ) : ℝ)) := by positivity
  have hright_argument_pos :
      0 < (((2 ^ k * m : ℕ) : ℝ) + 1) := by
    rw [← hright_cast]
    exact hright_pos
  rw [show evalFormalStencil (fun n => realDirichletPower s (n : ℝ))
      (centeredBracketStencil (2 ^ k * m) 1) =
      realDirichletPower s (((2 ^ k * m - 1 : ℕ) : ℝ)) -
        2 * realDirichletPower s (((2 ^ k * m : ℕ) : ℝ)) +
          realDirichletPower s (((2 ^ k * m + 1 : ℕ) : ℝ)) by
        simp [evalFormalStencil, centeredBracketStencil, atom]]
  rw [hleft_cast, hright_cast,
    realDirichletPower_eq_c2LegFunction s hleft_argument_pos,
    realDirichletPower_eq_c2LegFunction s hcenter_pos,
    realDirichletPower_eq_c2LegFunction s hright_argument_pos]
  simp [c2LegJetBracket, c2LegJetValue, c2LegLogWeight]

/-- The `1 + Σ g_c` finite chart is the original finite C2 camera readout,
with its seed visible. -/
theorem c2FiniteChartValue_eq_originalC2Stencil
    (cutoff : ℕ) (s : ℂ) :
    c2FiniteChartValue cutoff s =
      evalFormalStencil (fun n => realDirichletPower s (n : ℝ))
        (finiteStencil 2 cutoff) := by
  have hseed : evalFormalStencil
      (fun n => realDirichletPower s (n : ℝ)) (seedStencil 2) = 1 := by
    rw [seedStencil]
    simp [evalFormalStencil, atom, realDirichletPower]
  rw [c2FiniteCamera_allOrderReadout_eq_seed_add_fiberBracketSum
    (fun n => realDirichletPower s (n : ℝ)) cutoff]
  rw [hseed]
  unfold c2FiniteChartValue c2FiniteChartCenter
  congr 1
  apply Finset.sum_congr rfl
  intro index hi
  have hcenter :
      1 < 2 ^ c2AlignedIndexDepth index * c2AlignedIndexCore index := by
    rw [← c2AlignedCenter_eq_oddCoreCenter index]
    omega
  simpa using (c2FiniteFiberStencilBracket_eq_legJet s
    (c2AlignedIndexCore index) (c2AlignedIndexDepth index) hcenter).symm

/-- Identification with the repository's original finite C2 bracket chart. -/
theorem c2FiniteChartValue_eq_nativeFiniteCharacteristic
    (cutoff : ℕ) (s : ℂ) :
    c2FiniteChartValue cutoff s =
      finiteBracketCharacteristic 2 cutoff s := by
  rw [c2FiniteChartValue_eq_originalC2Stencil]
  have hsample : (fun n : ℕ => realDirichletPower s (n : ℝ)) =
      dirichletValue s := by
    funext n
    simp [realDirichletPower, dirichletValue]
  change (Finsupp.linearCombination ℤ
      (fun n : ℕ => realDirichletPower s (n : ℝ)))
      (finiteStencil 2 cutoff) = _
  rw [hsample]
  exact evalDirichletStencil_finiteStencil s 2 cutoff

/-- Abstract product-rule statement for a source with `V' = -iJ`. -/
theorem c2CompletedCompanion_eq_neg_deriv
    (L V J L' : ℂ → ℂ) (z : ℂ)
    (hL : HasDerivAt L (L' z) z)
    (hV : HasDerivAt V (-Complex.I * J z) z) :
    c2CompletedCompanion L L' V J z =
      -deriv (fun w : ℂ => c2ProductCharacteristic L V w) z := by
  unfold c2CompletedCompanion
  change Complex.I * L z * J z - L' z * V z = -deriv (L * V) z
  rw [(hL.mul hV).deriv]
  ring

/-- The companion changes by exactly the two-leg source correction. -/
theorem c2CompletedCompanion_sub_central_eq_legCorrection
    (L L' V J d E : ℂ → ℂ) (z : ℂ)
    (hJ : J z = d z + E z) :
    c2CompletedCompanion L L' V J z -
        c2CentralCompanion L L' V d z =
      Complex.I * L z * E z := by
  rw [c2CompletedCompanion, c2CentralCompanion, hJ]
  ring

/-- Normalized logarithmic response of the full companion. -/
def c2NormalizedResponse (L L' V J : ℂ → ℂ) (z : ℂ) : ℂ :=
  c2CompletedCompanion L L' V J z /
    (2 * c2ProductCharacteristic L V z)

/-- Normalized logarithmic response of the central companion. -/
def c2CentralNormalizedResponse (L L' V d : ℂ → ℂ) (z : ℂ) : ℂ :=
  c2CentralCompanion L L' V d z /
    (2 * c2ProductCharacteristic L V z)

theorem c2NormalizedResponse_sub_central_eq_legCorrection
    (L L' V J d E : ℂ → ℂ) (z : ℂ)
    (hJ : J z = d z + E z)
    (hL : L z ≠ 0) (hV : V z ≠ 0) :
    c2NormalizedResponse L L' V J z -
        c2CentralNormalizedResponse L L' V d z =
      Complex.I * E z / (2 * V z) := by
  unfold c2NormalizedResponse c2CentralNormalizedResponse
    c2CompletedCompanion c2CentralCompanion c2ProductCharacteristic
  rw [hJ]
  field_simp [hL, hV]
  ring

theorem c2CentralNormalizedResponse_eq_logarithmic_split
    (L L' V d : ℂ → ℂ) (z : ℂ)
    (hL : L z ≠ 0) (hV : V z ≠ 0) :
    c2CentralNormalizedResponse L L' V d z =
      -L' z / (2 * L z) + Complex.I * d z / (2 * V z) := by
  unfold c2CentralNormalizedResponse c2CentralCompanion
    c2ProductCharacteristic
  field_simp [hL, hV]
  ring

/-- Explicit polarized Wronskian of a characteristic and its companion. -/
def c2PolarizedWronskian
    (F C : ℂ → ℂ) (z w : ℂ) : ℂ :=
  star (F z) * C w - star (C z) * F w

/-- Polarized Wronskian using the central companion. -/
def c2CentralPolarizedWronskian
    (F C₀ : ℂ → ℂ) (z w : ℂ) : ℂ :=
  star (F z) * C₀ w - star (C₀ z) * F w

/-- The complete two-variable cross term. The sum of conjugate and direct
legs is retained. -/
theorem c2PolarizedWronskian_sub_central_eq_legCorrection
    (L V C₀ E : ℂ → ℂ) (z w : ℂ) :
    c2PolarizedWronskian (c2ProductCharacteristic L V)
        (fun x => C₀ x + Complex.I * L x * E x) z w -
      c2CentralPolarizedWronskian (c2ProductCharacteristic L V) C₀ z w =
      Complex.I * star (L z) * L w *
        (star (V z) * E w + star (E z) * V w) := by
  simp only [c2PolarizedWronskian, c2CentralPolarizedWronskian,
    c2ProductCharacteristic, star_add, star_mul, Complex.star_def,
    Complex.conj_I]
  ring

/-- Normalized polarized correction, with no diagonal quotient. -/
theorem c2PolarizedWronskian_normalized_legCorrection
    (L V C₀ E : ℂ → ℂ) (z w : ℂ)
    (hFz : c2ProductCharacteristic L V z ≠ 0)
    (hFw : c2ProductCharacteristic L V w ≠ 0) :
    (c2PolarizedWronskian (c2ProductCharacteristic L V)
        (fun x => C₀ x + Complex.I * L x * E x) z w -
      c2CentralPolarizedWronskian (c2ProductCharacteristic L V) C₀ z w) /
        (star (c2ProductCharacteristic L V z) *
          c2ProductCharacteristic L V w) =
      Complex.I *
        (E w / V w + star (E z) / star (V z)) := by
  have hLz : L z ≠ 0 := fun h => hFz (by simp [c2ProductCharacteristic, h])
  have hVz : V z ≠ 0 := fun h => hFz (by simp [c2ProductCharacteristic, h])
  have hLw : L w ≠ 0 := fun h => hFw (by simp [c2ProductCharacteristic, h])
  have hVw : V w ≠ 0 := fun h => hFw (by simp [c2ProductCharacteristic, h])
  rw [c2PolarizedWronskian_sub_central_eq_legCorrection]
  unfold c2ProductCharacteristic
  field_simp [hLz, hVz, hLw, hVw]
  simp only [star_mul, Complex.star_def]
  ring

/-- The original finite C2 chart on the complex height variable. -/
def c2FiniteChartHeightValue (cutoff : ℕ) (z : ℂ) : ℂ :=
  c2FiniteChartValue cutoff (c2SpectralLine z)

/-- First logarithmic jet on the same finite chart. -/
def c2FiniteChartHeightJet (cutoff : ℕ) (z : ℂ) : ℂ :=
  c2FiniteChartJet cutoff (c2SpectralLine z)

/-- Central logarithmic bracket sum on the same finite chart. -/
def c2FiniteChartHeightCentral (cutoff : ℕ) (z : ℂ) : ℂ :=
  c2FiniteChartCentral cutoff (c2SpectralLine z)

/-- Independent two-leg correction on the same finite chart. -/
def c2FiniteChartHeightLegCorrection (cutoff : ℕ) (z : ℂ) : ℂ :=
  c2FiniteChartLegCorrection cutoff (c2SpectralLine z)

/-- Derivative of the original completion-over-C2-factor dressing. -/
def c2CompletionDressingDerivative (z : ℂ) : ℂ :=
  deriv c2CompletionDressing z

/-- Completed finite C2 source `F = L V`. -/
def c2FiniteChartHeightCharacteristic (cutoff : ℕ) (z : ℂ) : ℂ :=
  c2ProductCharacteristic c2CompletionDressing
    (c2FiniteChartHeightValue cutoff) z

/-- Full finite companion `C = i L J - L' V`. -/
def c2FiniteChartHeightCompanion (cutoff : ℕ) (z : ℂ) : ℂ :=
  c2CompletedCompanion c2CompletionDressing
    c2CompletionDressingDerivative (c2FiniteChartHeightValue cutoff)
    (c2FiniteChartHeightJet cutoff) z

/-- Central proxy companion `C₀ = i L d - L' V`. -/
def c2FiniteChartHeightCentralCompanion (cutoff : ℕ) (z : ℂ) : ℂ :=
  c2CentralCompanion c2CompletionDressing
    c2CompletionDressingDerivative (c2FiniteChartHeightValue cutoff)
    (c2FiniteChartHeightCentral cutoff) z

/-- The finite C2 companion is the negative derivative of `F=L V`; only the
analytic differentiability of the original dressing is left as a local
hypothesis. -/
theorem c2FiniteChartHeightCompanion_eq_neg_deriv
    (cutoff : ℕ) (z : ℂ)
    (hL : HasDerivAt c2CompletionDressing
      (c2CompletionDressingDerivative z) z) :
    c2FiniteChartHeightCompanion cutoff z =
      -deriv (c2FiniteChartHeightCharacteristic cutoff) z := by
  exact c2CompletedCompanion_eq_neg_deriv c2CompletionDressing
    (c2FiniteChartHeightValue cutoff) (c2FiniteChartHeightJet cutoff)
    c2CompletionDressingDerivative z hL
    (c2FiniteChartValue_hasDerivAt_spectralLine cutoff z)

/-- Difference between the finite source companion and its central proxy. -/
theorem c2FiniteChartHeightCompanion_sub_central_eq_legCorrection
    (cutoff : ℕ) (z : ℂ) :
    c2FiniteChartHeightCompanion cutoff z -
        c2FiniteChartHeightCentralCompanion cutoff z =
      Complex.I * c2CompletionDressing z *
        c2FiniteChartHeightLegCorrection cutoff z := by
  exact c2CompletedCompanion_sub_central_eq_legCorrection
    c2CompletionDressing c2CompletionDressingDerivative
    (c2FiniteChartHeightValue cutoff) (c2FiniteChartHeightJet cutoff)
    (c2FiniteChartHeightCentral cutoff)
    (c2FiniteChartHeightLegCorrection cutoff) z
    (c2FiniteChartJet_eq_central_add_legCorrection cutoff
      (c2SpectralLine z))

/-- Polarization of the finite C2 source companion retains both crossed legs. -/
theorem c2FiniteChartHeightWronskian_sub_central_eq_legCorrection
    (cutoff : ℕ) (z w : ℂ) :
    c2PolarizedWronskian
        (fun x => c2FiniteChartHeightCharacteristic cutoff x)
        (fun x => c2FiniteChartHeightCompanion cutoff x) z w -
      c2CentralPolarizedWronskian
        (fun x => c2FiniteChartHeightCharacteristic cutoff x)
        (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w =
      Complex.I * star (c2CompletionDressing z) *
        c2CompletionDressing w *
          (star (c2FiniteChartHeightValue cutoff z) *
              c2FiniteChartHeightLegCorrection cutoff w +
            star (c2FiniteChartHeightLegCorrection cutoff z) *
              c2FiniteChartHeightValue cutoff w) := by
  have hcompanion (x : ℂ) :
      c2FiniteChartHeightCompanion cutoff x =
        c2FiniteChartHeightCentralCompanion cutoff x +
          Complex.I * c2CompletionDressing x *
            c2FiniteChartHeightLegCorrection cutoff x := by
    have h := c2FiniteChartHeightCompanion_sub_central_eq_legCorrection
      cutoff x
    calc
      c2FiniteChartHeightCompanion cutoff x =
          (c2FiniteChartHeightCompanion cutoff x -
            c2FiniteChartHeightCentralCompanion cutoff x) +
              c2FiniteChartHeightCentralCompanion cutoff x := by ring
      _ = (Complex.I * c2CompletionDressing x *
            c2FiniteChartHeightLegCorrection cutoff x) +
              c2FiniteChartHeightCentralCompanion cutoff x := by rw [h]
      _ = c2FiniteChartHeightCentralCompanion cutoff x +
            Complex.I * c2CompletionDressing x *
              c2FiniteChartHeightLegCorrection cutoff x := by ring
  have hC :
      (fun x => c2FiniteChartHeightCompanion cutoff x) = fun x =>
        c2FiniteChartHeightCentralCompanion cutoff x +
          Complex.I * c2CompletionDressing x *
            c2FiniteChartHeightLegCorrection cutoff x := by
    funext x
    exact hcompanion x
  rw [hC]
  change c2PolarizedWronskian
      (c2ProductCharacteristic c2CompletionDressing
        (c2FiniteChartHeightValue cutoff))
      (fun x => c2FiniteChartHeightCentralCompanion cutoff x +
        Complex.I * c2CompletionDressing x *
          c2FiniteChartHeightLegCorrection cutoff x) z w -
    c2CentralPolarizedWronskian
      (c2ProductCharacteristic c2CompletionDressing
        (c2FiniteChartHeightValue cutoff))
      (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w =
      Complex.I * star (c2CompletionDressing z) * c2CompletionDressing w *
        (star (c2FiniteChartHeightValue cutoff z) *
          c2FiniteChartHeightLegCorrection cutoff w +
          star (c2FiniteChartHeightLegCorrection cutoff z) *
            c2FiniteChartHeightValue cutoff w)
  exact c2PolarizedWronskian_sub_central_eq_legCorrection
    c2CompletionDressing (c2FiniteChartHeightValue cutoff)
    (fun x => c2FiniteChartHeightCentralCompanion cutoff x)
    (c2FiniteChartHeightLegCorrection cutoff) z w

/-- The normalized finite C2 polarized correction, with both source values
nonzero and no diagonal division. -/
theorem c2FiniteChartHeightWronskian_normalized_legCorrection
    (cutoff : ℕ) (z w : ℂ)
    (hFz : c2FiniteChartHeightCharacteristic cutoff z ≠ 0)
    (hFw : c2FiniteChartHeightCharacteristic cutoff w ≠ 0) :
    (c2PolarizedWronskian (fun x => c2FiniteChartHeightCharacteristic cutoff x)
        (fun x => c2FiniteChartHeightCompanion cutoff x) z w -
      c2CentralPolarizedWronskian
        (fun x => c2FiniteChartHeightCharacteristic cutoff x)
        (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w) /
        (star (c2FiniteChartHeightCharacteristic cutoff z) *
          c2FiniteChartHeightCharacteristic cutoff w) =
      Complex.I *
        (c2FiniteChartHeightLegCorrection cutoff w /
            c2FiniteChartHeightValue cutoff w +
          star (c2FiniteChartHeightLegCorrection cutoff z) /
            star (c2FiniteChartHeightValue cutoff z)) := by
  have hC :
      (fun x => c2FiniteChartHeightCompanion cutoff x) = fun x =>
        c2FiniteChartHeightCentralCompanion cutoff x +
          Complex.I * c2CompletionDressing x *
            c2FiniteChartHeightLegCorrection cutoff x := by
    funext x
    have h := c2FiniteChartHeightCompanion_sub_central_eq_legCorrection
      cutoff x
    calc
      c2FiniteChartHeightCompanion cutoff x =
          (c2FiniteChartHeightCompanion cutoff x -
            c2FiniteChartHeightCentralCompanion cutoff x) +
              c2FiniteChartHeightCentralCompanion cutoff x := by ring
      _ = (Complex.I * c2CompletionDressing x *
            c2FiniteChartHeightLegCorrection cutoff x) +
              c2FiniteChartHeightCentralCompanion cutoff x := by rw [h]
      _ = c2FiniteChartHeightCentralCompanion cutoff x +
            Complex.I * c2CompletionDressing x *
              c2FiniteChartHeightLegCorrection cutoff x := by ring
  rw [hC]
  have hFz' : c2ProductCharacteristic c2CompletionDressing
      (c2FiniteChartHeightValue cutoff) z ≠ 0 := by
    simpa [c2FiniteChartHeightCharacteristic] using hFz
  have hFw' : c2ProductCharacteristic c2CompletionDressing
      (c2FiniteChartHeightValue cutoff) w ≠ 0 := by
    simpa [c2FiniteChartHeightCharacteristic] using hFw
  change
    (c2PolarizedWronskian
        (c2ProductCharacteristic c2CompletionDressing
          (c2FiniteChartHeightValue cutoff))
        (fun x => c2FiniteChartHeightCentralCompanion cutoff x +
          Complex.I * c2CompletionDressing x *
            c2FiniteChartHeightLegCorrection cutoff x) z w -
      c2CentralPolarizedWronskian
        (c2ProductCharacteristic c2CompletionDressing
          (c2FiniteChartHeightValue cutoff))
        (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w) /
      (star (c2ProductCharacteristic c2CompletionDressing
          (c2FiniteChartHeightValue cutoff) z) *
        c2ProductCharacteristic c2CompletionDressing
          (c2FiniteChartHeightValue cutoff) w) =
      Complex.I *
        (c2FiniteChartHeightLegCorrection cutoff w /
            c2FiniteChartHeightValue cutoff w +
          star (c2FiniteChartHeightLegCorrection cutoff z) /
            star (c2FiniteChartHeightValue cutoff z))
  exact c2PolarizedWronskian_normalized_legCorrection
    c2CompletionDressing (c2FiniteChartHeightValue cutoff)
    (fun x => c2FiniteChartHeightCentralCompanion cutoff x)
    (c2FiniteChartHeightLegCorrection cutoff) z w hFz' hFw'


end
end CarrySelfAdjointOperator

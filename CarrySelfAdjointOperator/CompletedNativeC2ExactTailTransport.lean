import CarrySelfAdjointOperator.C2GeometryNativeSourceBridge
import CarrySelfAdjointOperator.CompletedNativeC2LegEnvelopeTransport
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSourceTrace
import CarrySelfAdjointOperator.CompletedC3PolarizedCameraCrossResidual
import CarrySelfAdjointOperator.CompletedProductJet
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open CarrySelfAdjointOperator.ChiralReturn

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-! ## The original C2 head and its exact omitted-center tail -/

/-- The exact C2 tail after `M` complete aligned cells.  Its summands are the
repository's original whole-center terms with their original seed and index
shift.  Here `M` is the C2 cell cutoff; it is independent of the radial index
`k` and Hankel order `n`. -/
def nativeC2ExactCenterTail (M : ℕ) (s : ℂ) : ℂ :=
  ∑' j : ℕ, centerBracketTerm 2 s (j + M)

theorem c2SpectralLine_eq_operatorHeightParameter (z : ℂ) :
    c2SpectralLine z = operatorHeightParameter z := by
  unfold c2SpectralLine operatorHeightParameter
  ring

private theorem genuineStrip_subset_nativeScalarDomain {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) : s ∈ nativeScalarDomain := by
  rcases hs with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- The original C2 factor cannot vanish in the open critical strip. -/
theorem c2Factor_ne_zero_of_genuineCriticalStrip {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) : factor 2 s ≠ 0 := by
  rcases hs with ⟨hlo, hhi⟩
  rw [factor_two, c2Factor_ne_zero_iff]
  constructor
  · intro h
    have hsum : (2 : ℂ) ^ (-s) + 1 = 0 := by simpa [add_comm] using h
    have hpow : (2 : ℂ) ^ (-s) = -1 :=
      (add_eq_zero_iff_eq_neg.mp hsum)
    have hnorm := congrArg norm hpow
    have hnorm' : (2 : ℝ) ^ (-s.re) = 1 := by
      have hnormPow : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
        simpa using Complex.norm_natCast_cpow_of_pos
          (n := 2) (by norm_num) (-s)
      rw [hnormPow, norm_neg, norm_one] at hnorm
      exact hnorm
    have hlt : (2 : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  · intro h
    have hpow : (2 : ℂ) ^ (1 - s) = 1 := (sub_eq_zero.mp h).symm
    have hnorm := congrArg norm hpow
    have hnorm' : (2 : ℝ) ^ (1 - s.re) = 1 := by
      have hnormPow : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
        rw [show (2 : ℂ) = (2 : ℕ) by norm_num,
          Complex.norm_natCast_cpow_of_pos (by norm_num : 0 < 2)]
        norm_num [Complex.sub_re, Complex.one_re]
      rw [hnormPow, norm_one] at hnorm
      exact hnorm
    have hgt : 1 < (2 : ℝ) ^ (1 - s.re) :=
      Real.one_lt_rpow (by norm_num) (by linarith)
    linarith

/-- The finite chart in Luna E is definitionally the original C2 camera head
at the spectral parameter `s(z)`.  The source denominator remains in the
carrier weight; this equality only identifies the scalar numerator. -/
theorem c2FiniteChartHeightValue_eq_originalC2Characteristic_at
    (M : ℕ) (z : ℂ) :
    c2FiniteChartHeightValue M z =
      finiteBracketCharacteristic 2 M (operatorHeightParameter z) := by
  rw [c2FiniteChartHeightValue,
    c2FiniteChartValue_eq_nativeFiniteCharacteristic]
  congr 2
  exact c2SpectralLine_eq_operatorHeightParameter z

/-- Luna E's completed finite value numerator is exactly the original C2
completion dressing times the native finite C2 head. Its denominator is still
the separate, original Hermite--Biehler carrier coordinate. -/
theorem c2FiniteChartHeightCharacteristic_eq_dressing_mul_originalHead
    (M : ℕ) (z : ℂ) :
    c2FiniteChartHeightCharacteristic M z =
      c2CompletionDressing z * finiteBracketCharacteristic 2 M
        (operatorHeightParameter z) := by
  unfold c2FiniteChartHeightCharacteristic c2ProductCharacteristic
  rw [c2FiniteChartHeightValue_eq_originalC2Characteristic_at]

/-- Exact scalar transport of the omitted whole-center tail through the
original C2 completion factor.  This uses `H_M + T_M = B₂ N` and the original
`L=A/B₂`; no finite-chart denominator is reconstructed. -/
theorem completedNativeC2Characteristic_sub_finite_eq_completion_mul_exactTail
    (M : ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorCharacteristic z -
        c2FiniteChartHeightCharacteristic M z =
      c2CompletionDressing z *
        nativeC2ExactCenterTail M (operatorHeightParameter z) := by
  let s := operatorHeightParameter z
  let A := nativeXiCompletionFactor z
  let B := factor 2 s
  let H := finiteBracketCharacteristic 2 M s
  let T := nativeC2ExactCenterTail M s
  have hsNative : s ∈ nativeScalarDomain :=
    genuineStrip_subset_nativeScalarDomain hs
  have hB : B ≠ 0 := by
    dsimp [B]
    exact c2Factor_ne_zero_of_genuineCriticalStrip hs
  have hhead : c2FiniteChartHeightValue M z = H := by
    dsimp [H, s]
    exact c2FiniteChartHeightValue_eq_originalC2Characteristic_at M z
  have hledger : H + T = B * nativeScalar s := by
    simpa [H, T, B, nativeC2ExactCenterTail, factor_two] using
      canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar
        M hsNative
  change A * nativeScalar s -
      c2CompletionDressing z * c2FiniteChartHeightValue M z =
    c2CompletionDressing z * T
  rw [hhead]
  dsimp [A, B, H, T]
  unfold c2CompletionDressing
  rw [c2SpectralLine_eq_operatorHeightParameter]
  change nativeXiCompletionFactor z * nativeScalar s -
      (nativeXiCompletionFactor z / factor 2 s) * H =
    (nativeXiCompletionFactor z / factor 2 s) * T
  have htail : factor 2 s * nativeScalar s - H = T := by
    calc
      factor 2 s * nativeScalar s - H = (H + T) - H := by
        rw [← hledger]
      _ = T := by ring
  calc
    nativeXiCompletionFactor z * nativeScalar s -
        (nativeXiCompletionFactor z / factor 2 s) * H =
      (nativeXiCompletionFactor z / factor 2 s) *
        (factor 2 s * nativeScalar s - H) := by
        have hcancel :
            (nativeXiCompletionFactor z / factor 2 s) * factor 2 s =
              nativeXiCompletionFactor z := div_mul_cancel₀ _ hB
        calc
          _ = ((nativeXiCompletionFactor z / factor 2 s) * factor 2 s) *
                nativeScalar s -
                (nativeXiCompletionFactor z / factor 2 s) * H := by
                  rw [hcancel]
          _ = _ := by ring
    _ = (nativeXiCompletionFactor z / factor 2 s) * T := by rw [htail]

/-- The exact tail is also the difference between the full C2 bracket and
the original finite head.  This exposes the locally uniform convergence
interface without changing the tail's definition. -/
theorem nativeC2ExactCenterTail_eq_bracket_sub_head
    (M : ℕ) {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    nativeC2ExactCenterTail M s =
      bracketCharacteristic 2 s - finiteBracketCharacteristic 2 M s := by
  have hheadTail :=
    canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar
      M hs
  have hbracket := bracketCharacteristic_eq_factor_mul_nativeScalar
    (camera := 2) (by norm_num) hs
  have hsum :
      finiteBracketCharacteristic 2 M s + nativeC2ExactCenterTail M s =
        bracketCharacteristic 2 s := by
    simpa [nativeC2ExactCenterTail, factor_two] using hheadTail.trans hbracket.symm
  linear_combination hsum

/-- The derivative of the exact series tail is the derivative of the full C2
bracket minus the derivative of its finite head.  The local equality is on
the open native scalar domain, where the original head--tail identity holds. -/
theorem deriv_nativeC2ExactCenterTail_eq
    (M : ℕ) {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    deriv (nativeC2ExactCenterTail M) s =
      deriv (bracketCharacteristic 2) s -
        deriv (finiteBracketCharacteristic 2 M) s := by
  have hlocal : nativeC2ExactCenterTail M =ᶠ[nhds s]
      (fun u => bracketCharacteristic 2 u -
        finiteBracketCharacteristic 2 M u) := by
    filter_upwards [isOpen_nativeScalarDomain.mem_nhds hs] with u hu
    exact nativeC2ExactCenterTail_eq_bracket_sub_head M hu
  rw [hlocal.deriv_eq]
  change deriv (bracketCharacteristic 2 -
    finiteBracketCharacteristic 2 M) s = _
  rw [deriv_sub]
  · exact (bracketCharacteristic_differentiableOn
      (by norm_num : 2 ≤ 2)).differentiableAt
        (isOpen_bracketDomain.mem_nhds (by
          simpa [nativeScalarDomain, bracketDomain] using hs.1))
  · exact (finiteBracketCharacteristic_differentiable
      (by norm_num : 2 ≤ 2) M).differentiableAt

/-- The exact omitted-center value tail vanishes with the original C2 cutoff
at every point of the native scalar domain. -/
theorem nativeC2ExactCenterTail_tendsto_zero
    {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    Tendsto (fun M : ℕ => nativeC2ExactCenterTail M s)
      atTop (nhds 0) := by
  have hfinite := finiteBracketCharacteristic_tendsto
    (by norm_num : 2 ≤ 2) hs.1
  have hconstant : Tendsto (fun _ : ℕ => bracketCharacteristic 2 s)
      atTop (nhds (bracketCharacteristic 2 s)) := tendsto_const_nhds
  have h := hconstant.sub hfinite
  have hseq : (fun M : ℕ => nativeC2ExactCenterTail M s) =
      (fun M => bracketCharacteristic 2 s -
        finiteBracketCharacteristic 2 M s) := by
    funext M
    exact nativeC2ExactCenterTail_eq_bracket_sub_head M hs
  rw [hseq]
  simpa using h

/-- The differentiated exact tail also vanishes with the original C2 cutoff.
This is the derivative convergence theorem for the locally uniform finite
characteristic series, transported through the exact whole-center identity. -/
theorem deriv_nativeC2ExactCenterTail_tendsto_zero
    {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    Tendsto (fun M : ℕ => deriv (nativeC2ExactCenterTail M) s)
      atTop (nhds 0) := by
  have hsBracket : s ∈ bracketDomain := by
    simpa [nativeScalarDomain, bracketDomain] using hs.1
  have hfinite := deriv_finiteBracketCharacteristic_tendsto
    (by norm_num : 2 ≤ 2) hsBracket
  have hconstant : Tendsto (fun _ : ℕ => deriv (bracketCharacteristic 2) s)
      atTop (nhds (deriv (bracketCharacteristic 2) s)) := tendsto_const_nhds
  have h := hconstant.sub hfinite
  have hseq : (fun M : ℕ => deriv (nativeC2ExactCenterTail M) s) =
      (fun M => deriv (bracketCharacteristic 2) s -
        deriv (finiteBracketCharacteristic 2 M) s) := by
    funext M
    exact deriv_nativeC2ExactCenterTail_eq M hs
  rw [hseq]
  simpa using h

/-- Differentiability of the original completion-over-C2-factor dressing on
the open strip, with the same C2 factor as the head--tail identity. -/
theorem c2CompletionDressing_hasDerivAt
    (z : ℂ) (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    HasDerivAt c2CompletionDressing
      (c2CompletionDressingDerivative z) z := by
  have hsLine : c2SpectralLine z ∈ genuineCriticalStrip := by
    rw [c2SpectralLine_eq_operatorHeightParameter]
    exact hs
  have hden : factor 2 (c2SpectralLine z) ≠ 0 := by
    simpa only [factor_two] using
      c2Factor_ne_zero_of_genuineCriticalStrip hsLine
  have hxi : DifferentiableAt ℂ nativeXiCompletionFactor z :=
    nativeXiCompletionFactor_differentiableAt hs
  have hline : DifferentiableAt ℂ c2SpectralLine z :=
    (hasDerivAt_c2SpectralLine z).differentiableAt
  have hfactorAtLine :
      DifferentiableAt ℂ (fun s : ℂ => factor 2 s) (c2SpectralLine z) :=
    (factor_differentiable (by norm_num : 2 ≤ 2)).differentiableAt
  have hdenDiff : DifferentiableAt ℂ
      (fun w : ℂ => factor 2 (c2SpectralLine w)) z :=
    hfactorAtLine.comp z hline
  have hLdiff : DifferentiableAt ℂ c2CompletionDressing z := by
    change DifferentiableAt ℂ
      (fun w : ℂ => nativeXiCompletionFactor w /
        factor 2 (c2SpectralLine w)) z
    exact hxi.div hdenDiff hden
  exact hLdiff.hasDerivAt

/-- Quotient-rule expansion of `L'`.  It retains the derivative of the
completion factor, the derivative of the original C2 camera factor, and the
height rotation `s'(z)=i` explicitly. -/
theorem c2CompletionDressingDerivative_eq_originalFactorDerivatives
    (z : ℂ) (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    c2CompletionDressingDerivative z =
      (deriv nativeXiCompletionFactor z *
          factor 2 (c2SpectralLine z) -
        nativeXiCompletionFactor z *
          (deriv (fun s : ℂ => factor 2 s) (c2SpectralLine z) *
            Complex.I)) /
        factor 2 (c2SpectralLine z) ^ 2 := by
  have hsLine : c2SpectralLine z ∈ genuineCriticalStrip := by
    rw [c2SpectralLine_eq_operatorHeightParameter]
    exact hs
  have hden : factor 2 (c2SpectralLine z) ≠ 0 := by
    simpa only [factor_two] using
      c2Factor_ne_zero_of_genuineCriticalStrip hsLine
  have hxi : DifferentiableAt ℂ nativeXiCompletionFactor z :=
    nativeXiCompletionFactor_differentiableAt hs
  have hline : DifferentiableAt ℂ c2SpectralLine z :=
    (hasDerivAt_c2SpectralLine z).differentiableAt
  have hfactorAtLine :
      DifferentiableAt ℂ (fun s : ℂ => factor 2 s) (c2SpectralLine z) :=
    (factor_differentiable (by norm_num : 2 ≤ 2)).differentiableAt
  have hdenDiff : DifferentiableAt ℂ
      (fun w : ℂ => factor 2 (c2SpectralLine w)) z :=
    hfactorAtLine.comp z hline
  have hdenHas : HasDerivAt
      (fun w : ℂ => factor 2 (c2SpectralLine w))
      (deriv (fun s : ℂ => factor 2 s) (c2SpectralLine z) * Complex.I) z := by
    have h := hfactorAtLine.hasDerivAt.comp z (hasDerivAt_c2SpectralLine z)
    simpa only [Function.comp_def] using h
  have hdenDeriv : deriv
      (fun w : ℂ => factor 2 (c2SpectralLine w)) z =
        deriv (fun s : ℂ => factor 2 s) (c2SpectralLine z) * Complex.I :=
    hdenHas.deriv
  change deriv (nativeXiCompletionFactor /
      (fun w : ℂ => factor 2 (c2SpectralLine w))) z = _
  rw [deriv_div hxi hdenDiff hden, hdenDeriv]

/-- The exact differentiated tail, including the chain factor `i` from
`s(z)=1/2+iz`. -/
theorem nativeC2ExactCenterTailHeight_hasDerivAt
    (M : ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    HasDerivAt (fun w : ℂ =>
        nativeC2ExactCenterTail M (c2SpectralLine w))
      (Complex.I * deriv (nativeC2ExactCenterTail M)
        (c2SpectralLine z)) z := by
  have hsLine : c2SpectralLine z ∈ nativeScalarDomain := by
    rw [c2SpectralLine_eq_operatorHeightParameter]
    exact genuineStrip_subset_nativeScalarDomain hs
  have hlocal : nativeC2ExactCenterTail M =ᶠ[nhds (c2SpectralLine z)]
      (fun u => bracketCharacteristic 2 u -
        finiteBracketCharacteristic 2 M u) := by
    filter_upwards [isOpen_nativeScalarDomain.mem_nhds hsLine] with u hu
    exact nativeC2ExactCenterTail_eq_bracket_sub_head M hu
  have hbracketDiff : DifferentiableAt ℂ (bracketCharacteristic 2)
      (c2SpectralLine z) :=
    (bracketCharacteristic_differentiableOn
      (by norm_num : 2 ≤ 2)).differentiableAt
        (isOpen_bracketDomain.mem_nhds (by
          simpa [nativeScalarDomain, bracketDomain] using hsLine.1))
  have hheadDiff : DifferentiableAt ℂ
      (finiteBracketCharacteristic 2 M) (c2SpectralLine z) :=
    (finiteBracketCharacteristic_differentiable
      (by norm_num : 2 ≤ 2) M).differentiableAt
  have htail : HasDerivAt (nativeC2ExactCenterTail M)
      (deriv (nativeC2ExactCenterTail M) (c2SpectralLine z))
      (c2SpectralLine z) := by
    have h := (hbracketDiff.sub hheadDiff).hasDerivAt
    have h' := h.congr_of_eventuallyEq hlocal
    have hderivValue :
        deriv (bracketCharacteristic 2 -
          finiteBracketCharacteristic 2 M) (c2SpectralLine z) =
        deriv (nativeC2ExactCenterTail M) (c2SpectralLine z) := by
      rw [deriv_sub hbracketDiff hheadDiff]
      exact (deriv_nativeC2ExactCenterTail_eq M hsLine).symm
    rw [hderivValue] at h'
    exact h'
  have hcomp := htail.comp z (hasDerivAt_c2SpectralLine z)
  simpa only [Function.comp_def, mul_comm] using hcomp

/-- The companion difference is the negative derivative of the exact
completion-weighted C2 tail.  All derivative channels remain in this formula
before any source synthesis or norm estimate. -/
theorem completedNativeC2Companion_sub_finite_eq_neg_deriv_exactTail
    (M : ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorBoundaryCompanion z -
        c2FiniteChartHeightCompanion M z =
      -deriv (fun w : ℂ =>
        c2CompletionDressing w *
          nativeC2ExactCenterTail M (c2SpectralLine w)) z := by
  have hL := c2CompletionDressing_hasDerivAt z hs
  have hsDomain : z ∈ completedNativeHeightDomain := by
    simpa [completedNativeHeightDomain] using hs
  have hF : DifferentiableAt ℂ completedNativeOperatorCharacteristic z :=
    (completedNativeOperatorCharacteristic_analyticAt hsDomain).differentiableAt
  have hFM : DifferentiableAt ℂ
      (c2FiniteChartHeightCharacteristic M) z := by
    change DifferentiableAt ℂ
      (c2CompletionDressing * c2FiniteChartHeightValue M) z
    exact hL.differentiableAt.mul
      (c2FiniteChartValue_hasDerivAt_spectralLine M z).differentiableAt
  have hT := nativeC2ExactCenterTailHeight_hasDerivAt M z hs
  have hprod := hL.mul hT
  have hlocal : (fun w : ℂ =>
      completedNativeOperatorCharacteristic w -
        c2FiniteChartHeightCharacteristic M w) =ᶠ[nhds z]
      (fun w : ℂ => c2CompletionDressing w *
        nativeC2ExactCenterTail M (c2SpectralLine w)) := by
    filter_upwards [isOpen_completedNativeHeightDomain.mem_nhds hsDomain]
      with w hw
    simpa only [c2SpectralLine_eq_operatorHeightParameter] using
      completedNativeC2Characteristic_sub_finite_eq_completion_mul_exactTail
        M w (by simpa [completedNativeHeightDomain] using hw)
  have hderiv : deriv (fun w : ℂ =>
      completedNativeOperatorCharacteristic w -
        c2FiniteChartHeightCharacteristic M w) z =
      deriv (fun w : ℂ => c2CompletionDressing w *
        nativeC2ExactCenterTail M (c2SpectralLine w)) z := hlocal.deriv_eq
  calc
    completedNativeOperatorBoundaryCompanion z -
        c2FiniteChartHeightCompanion M z =
      -deriv completedNativeOperatorCharacteristic z -
        (-deriv (c2FiniteChartHeightCharacteristic M) z) := by
          rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv,
            c2FiniteChartHeightCompanion_eq_neg_deriv M z hL]
    _ = -deriv (fun w : ℂ =>
        completedNativeOperatorCharacteristic w -
          c2FiniteChartHeightCharacteristic M w) z := by
          change -deriv completedNativeOperatorCharacteristic z -
            (-deriv (c2FiniteChartHeightCharacteristic M) z) =
            -(deriv (completedNativeOperatorCharacteristic -
              c2FiniteChartHeightCharacteristic M) z)
          rw [deriv_sub hF hFM]
          ring
    _ = -deriv (fun w : ℂ => c2CompletionDressing w *
        nativeC2ExactCenterTail M (c2SpectralLine w)) z := by rw [hderiv]

/-- Fully expanded companion-tail formula.  It displays the derivative of
the completion-over-camera dressing, the tail derivative, and `s'(z)=i`. -/
theorem completedNativeC2Companion_sub_finite_eq_expanded_exactTail
    (M : ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorBoundaryCompanion z -
        c2FiniteChartHeightCompanion M z =
      -(c2CompletionDressingDerivative z *
          nativeC2ExactCenterTail M (c2SpectralLine z) +
        c2CompletionDressing z * Complex.I *
          deriv (nativeC2ExactCenterTail M) (c2SpectralLine z)) := by
  rw [completedNativeC2Companion_sub_finite_eq_neg_deriv_exactTail M z hs]
  have hL := c2CompletionDressing_hasDerivAt z hs
  have hT := nativeC2ExactCenterTailHeight_hasDerivAt M z hs
  change -deriv (c2CompletionDressing *
      (fun w : ℂ => nativeC2ExactCenterTail M (c2SpectralLine w))) z = _
  rw [(hL.mul hT).deriv]
  ring

/-! ## Transport into the original finite-node Cauchy carrier -/

/-- Exact value-tail synthesis at the Luna E source nodes.  It uses the
original source weights and radial Cauchy states verbatim. -/
def nativeSourceC2ExactValueTailSynthesis
    (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  c2CauchySynthesis
    (fun i => nativeSourceC2SourceWeight n k x i *
      c2CompletionDressing (canonicalCompletedC3RadialTiltPoint k i) *
      nativeC2ExactCenterTail M
        (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i)))
    (fun i => completedNativeRadialChiralCauchyState k i)

/-- Exact companion-tail synthesis at the same nodes, weights, and states.
Its scalar coefficient is the expanded negative derivative, with the C2
camera and completion derivatives, the exact-tail derivative, and the factor
`i` all retained. -/
def nativeSourceC2ExactCompanionTailSynthesis
    (n k M : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  c2CauchySynthesis
    (fun i => nativeSourceC2SourceWeight n k x i *
      (-(c2CompletionDressingDerivative
          (canonicalCompletedC3RadialTiltPoint k i) *
          nativeC2ExactCenterTail M
            (c2SpectralLine (canonicalCompletedC3RadialTiltPoint k i)) +
        c2CompletionDressing (canonicalCompletedC3RadialTiltPoint k i) *
          Complex.I * deriv (nativeC2ExactCenterTail M)
            (c2SpectralLine (canonicalCompletedC3RadialTiltPoint k i)))) )
    (fun i => completedNativeRadialChiralCauchyState k i)

/-- The value tail from the PR #116 definition is exactly the finite
synthesis of `L(z_i) T_M(s(z_i))`.  The old Hermite--Biehler denominator and
the complete radial vectors are unchanged. -/
theorem nativeSourceC2ValueTail_eq_exactCenterTailSynthesis
    (n k M : ℕ) (x : Fin (2*n) → ℂ)
    (hstrip : ∀ i : Fin (2*n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    nativeSourceC2ValueTail n k M x =
      nativeSourceC2ExactValueTailSynthesis n k M x := by
  rw [nativeSourceC2ValueTail,
    sourceValue_one_eq_nativeSourceC2SourceSynthesis]
  unfold nativeSourceC2ApproxValue nativeSourceC2ExactValueTailSynthesis
    c2CauchyValueSynthesis
  simp only [c2CauchySynthesis]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sub_smul]
  have hscalar :=
    completedNativeC2Characteristic_sub_finite_eq_completion_mul_exactTail
      M (canonicalCompletedC3RadialTiltPoint k i) (hstrip i)
  rw [show nativeSourceC2SourceWeight n k x i *
        completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k i) -
        nativeSourceC2SourceWeight n k x i *
          c2FiniteChartHeightCharacteristic M
            (canonicalCompletedC3RadialTiltPoint k i) =
      nativeSourceC2SourceWeight n k x i *
        (completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) -
          c2FiniteChartHeightCharacteristic M
            (canonicalCompletedC3RadialTiltPoint k i)) by ring]
  rw [hscalar]
  congr 1
  ring

/-- At radius one the complete companion is the original source synthesis
with `-F'` at each radial node. -/
theorem sourceCompanion_one_eq_nativeSourceC2CompanionSynthesis
    (n k : ℕ) (x : Fin (2*n) → ℂ) :
    sourceCompanion k (nativeSourceChiralJetInput n k x) 1 =
      c2CauchyCompanionSynthesis (nativeSourceC2SourceWeight n k x)
        (fun i => completedNativeOperatorBoundaryCompanion
          (canonicalCompletedC3RadialTiltPoint k i))
        (fun i => completedNativeRadialChiralCauchyState k i) := by
  unfold ChiralReturn.sourceCompanion c2CauchyCompanionSynthesis
    c2CauchySynthesis nativeSourceC2SourceWeight
  apply Finset.sum_congr rfl
  intro i hi
  simp [one_pow, completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  rw [← neg_smul]
  congr 1
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The companion tail from Luna E is exactly the synthesis of the
negative derivative of the completion-weighted exact C2 tail. -/
theorem nativeSourceC2CompanionTail_eq_exactCenterTailSynthesis
    (n k M : ℕ) (x : Fin (2*n) → ℂ)
    (hstrip : ∀ i : Fin (2*n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    nativeSourceC2CompanionTail n k M x =
      nativeSourceC2ExactCompanionTailSynthesis n k M x := by
  rw [nativeSourceC2CompanionTail,
    sourceCompanion_one_eq_nativeSourceC2CompanionSynthesis]
  unfold nativeSourceC2ApproxCompanion nativeSourceC2ExactCompanionTailSynthesis
    c2CauchyCompanionSynthesis
  simp only [c2CauchySynthesis]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sub_smul]
  have hscalar := completedNativeC2Companion_sub_finite_eq_expanded_exactTail
    M (canonicalCompletedC3RadialTiltPoint k i) (hstrip i)
  rw [show nativeSourceC2SourceWeight n k x i *
        completedNativeOperatorBoundaryCompanion
          (canonicalCompletedC3RadialTiltPoint k i) -
        nativeSourceC2SourceWeight n k x i *
          c2FiniteChartHeightCompanion M
            (canonicalCompletedC3RadialTiltPoint k i) =
      nativeSourceC2SourceWeight n k x i *
        (completedNativeOperatorBoundaryCompanion
            (canonicalCompletedC3RadialTiltPoint k i) -
          c2FiniteChartHeightCompanion M
            (canonicalCompletedC3RadialTiltPoint k i)) by ring]
  rw [hscalar]

end
end CarrySelfAdjointOperator

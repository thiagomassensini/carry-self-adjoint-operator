import CarrySelfAdjointOperator.BridgeFirstGreenProtocol
import CarrySelfAdjointOperator.CompletedProductJet
import CPFormal.Analytic.CpBracketHolomorphic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open scoped BigOperators Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Metric Set

noncomputable section

def canonicalC3LogJetCutoffTail (M : ℕ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, canonicalLogBracketBlock (k + M) s

theorem hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm
    (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    HasDerivAt (fun u : ℂ => natDirichletTerm u n)
      (-natLogDirichletTerm s n) s := by
  have hnComplex : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  have hpow :=
    (hasDerivAt_neg' s).const_cpow (c := (n : ℂ)) (Or.inl hnComplex)
  convert hpow using 1
  · funext u
    simp [natDirichletTerm, dirichletTerm]
  · rw [← Complex.natCast_log]
    simp only [natLogDirichletTerm, natDirichletTerm, dirichletTerm,
      Int.cast_natCast]
    ring

theorem hasDerivAt_realCpSaturatedBracket_three_eq_neg_logBracket
    (m : ℕ) (s : ℂ) :
    HasDerivAt (realCpSaturatedBracket 3 m)
      (-canonicalLogBracketBlock m s) s := by
  have hleft :=
    hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm
      (3 * m + 2) (by omega) s
  have hcenter :=
    hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm
      (3 * m + 3) (by omega) s
  have hright :=
    hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm
      (3 * m + 4) (by omega) s
  rw [show realCpSaturatedBracket 3 m = fun u : ℂ =>
      natDirichletTerm u (3 * m + 2) -
        2 * natDirichletTerm u (3 * m + 3) +
          natDirichletTerm u (3 * m + 4) by
    funext u
    exact realCpSaturatedBracket_three_eq_values m u]
  refine ((hleft.sub (hcenter.const_mul 2)).add hright).congr_deriv ?_
  unfold canonicalLogBracketBlock
  rw [positiveLogDirichletValue_eq_natLogDirichletTerm,
    positiveLogDirichletValue_eq_natLogDirichletTerm,
    positiveLogDirichletValue_eq_natLogDirichletTerm]
  ring

theorem hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet
    (M : ℕ) (s : ℂ) :
    HasDerivAt (finiteBracketedDirichletChart 3 M)
      (-finiteCanonicalLogBracketChart M s) s := by
  have hseedFunction :
      (fun u : ℂ =>
        CPFormal.Genuine.Cp.seedSum 3 (dirichletTerm u)) =
      (fun _ : ℂ => (1 : ℂ)) := by
    funext u
    exact seedSum_three_dirichlet_eq_one u
  have hseed : HasDerivAt
      (fun u : ℂ =>
        CPFormal.Genuine.Cp.seedSum 3 (dirichletTerm u)) 0 s := by
    exact (hasDerivAt_const (x := s) (c := (1 : ℂ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => congrFun hseedFunction u)
  have hblocks : HasDerivAt
      (fun u : ℂ =>
        ∑ m ∈ Finset.range M, realCpSaturatedBracket 3 m u)
      (∑ m ∈ Finset.range M, -canonicalLogBracketBlock m s) s := by
    exact HasDerivAt.fun_sum fun m _hm =>
      hasDerivAt_realCpSaturatedBracket_three_eq_neg_logBracket m s
  have htotal := hseed.add hblocks
  change HasDerivAt
    ((fun u : ℂ =>
        CPFormal.Genuine.Cp.seedSum 3 (dirichletTerm u)) +
      fun u : ℂ =>
        ∑ m ∈ Finset.range M, realCpSaturatedBracket 3 m u)
    (-finiteCanonicalLogBracketChart M s) s
  refine htotal.congr_deriv ?_
  simp [finiteCanonicalLogBracketChart, Finset.sum_neg_distrib]

theorem finiteCanonicalLogBracketChart_eq_neg_deriv_valueChart
    (M : ℕ) (s : ℂ) :
    finiteCanonicalLogBracketChart M s =
      -deriv (finiteBracketedDirichletChart 3 M) s := by
  rw [(hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet
    M s).deriv]
  ring

theorem hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail
    (M : ℕ) {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    HasDerivAt (realCpBracketCutoffTail 3 M)
      (-canonicalC3LogJetCutoffTail M s) s := by
  let R := bracketNeighborhoodRadius s
  let U : Set ℂ := ball s R
  let u : ℕ → ℝ := fun k =>
    localCpBracketMajorantConstant 3 s R *
      (((k + M + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor s - 2))
  have hR : 0 < R := bracketNeighborhoodRadius_pos hs
  have hu : Summable u := by
    have hmajorant := summable_localCpBracketMajorant 3 hs
    have hshift := (summable_nat_add_iff M).2 hmajorant
    simpa [u, R, Nat.add_assoc] using hshift
  have hUOpen : IsOpen U := isOpen_ball
  have hsU : s ∈ U := by
    change dist s s < R
    simpa using hR
  have hsumDeriv :
      HasSum
        (fun k : ℕ =>
          deriv (realCpSaturatedBracket 3 (k + M)) s)
        (deriv (realCpBracketCutoffTail 3 M) s) := by
    change HasSum
      (fun k : ℕ => deriv (realCpSaturatedBracket 3 (k + M)) s)
      (deriv (fun w : ℂ =>
        ∑' k : ℕ, realCpSaturatedBracket 3 (k + M) w) s)
    exact Complex.hasSum_deriv_of_summable_norm
        (F := fun k : ℕ => realCpSaturatedBracket 3 (k + M))
        (U := U) (z := s) hu
        (fun k =>
          (differentiable_realCpSaturatedBracket
            3 (k + M) (by norm_num)).differentiableOn)
        hUOpen
        (fun k w hw => by
          simpa [u, U, R, Nat.add_assoc] using
            norm_realCpSaturatedBracket_le_local
              3 (by norm_num) hs hw (k + M))
        hsU
  have hsumNegLog :
      HasSum
        (fun k : ℕ => -canonicalLogBracketBlock (k + M) s)
        (deriv (realCpBracketCutoffTail 3 M) s) := by
    have hterm (k : ℕ) :
        deriv (realCpSaturatedBracket 3 (k + M)) s =
          -canonicalLogBracketBlock (k + M) s :=
      (hasDerivAt_realCpSaturatedBracket_three_eq_neg_logBracket
        (k + M) s).deriv
    exact HasSum.congr_fun hsumDeriv (fun k => (hterm k).symm)
  have hsumLog := hsumNegLog.neg
  have hlogEq :
      canonicalC3LogJetCutoffTail M s =
        -deriv (realCpBracketCutoffTail 3 M) s := by
    simpa [canonicalC3LogJetCutoffTail] using hsumLog.tsum_eq
  have htailOn : DifferentiableOn ℂ
      (fun w : ℂ =>
        ∑' k : ℕ, realCpSaturatedBracket 3 (k + M) w) U := by
    exact Complex.differentiableOn_tsum_of_summable_norm hu
      (fun k =>
        (differentiable_realCpSaturatedBracket
          3 (k + M) (by norm_num)).differentiableOn)
      hUOpen
      (fun k w hw => by
        simpa [u, U, R, Nat.add_assoc] using
          norm_realCpSaturatedBracket_le_local
            3 (by norm_num) hs hw (k + M))
  have hdiff : DifferentiableAt ℂ (realCpBracketCutoffTail 3 M) s := by
    change DifferentiableAt ℂ
      (fun w : ℂ =>
        ∑' k : ℕ, realCpSaturatedBracket 3 (k + M) w) s
    exact htailOn.differentiableAt (hUOpen.mem_nhds hsU)
  refine hdiff.hasDerivAt.congr_deriv ?_
  rw [hlogEq]
  ring

theorem canonicalC3LogJetCutoffTail_eq_neg_deriv_valueTail
    (M : ℕ) {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    canonicalC3LogJetCutoffTail M s =
      -deriv (realCpBracketCutoffTail 3 M) s := by
  rw [(hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail M hs).deriv]
  ring

def canonicalCompletedC3EnrichedTfvdValueTailReadout (s : ℂ) : ℂ :=
  NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout
    1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s

def canonicalCompletedC3EnrichedTfvdLogJetTailReadout (s : ℂ) : ℂ :=
  (CanonicalCompletedC3EnrichedTfvdTransport s).logJetReadout +
    canonicalC3LogJetCutoffTail 1 s

theorem hasDerivAt_canonicalCompletedC3EnrichedTfvdValueTailReadout
    {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    HasDerivAt canonicalCompletedC3EnrichedTfvdValueTailReadout
      (-canonicalCompletedC3EnrichedTfvdLogJetTailReadout s) s := by
  have hheadBase :=
    hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet 1 s
  have hhead : HasDerivAt
      (fun u : ℂ =>
        (CanonicalCompletedC3EnrichedTfvdTransport u).valueReadout)
      (-finiteCanonicalLogBracketChart 1 s) s := by
    exact hheadBase.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        (canonicalCompletedC3EnrichedTfvdTransport_components u).1)
  have htail :=
    hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail 1 hs
  have hsum := hhead.add htail
  change HasDerivAt
    ((fun u : ℂ =>
        (CanonicalCompletedC3EnrichedTfvdTransport u).valueReadout) +
      realCpBracketCutoffTail 3 1)
    (-canonicalCompletedC3EnrichedTfvdLogJetTailReadout s) s
  refine hsum.congr_deriv ?_
  unfold canonicalCompletedC3EnrichedTfvdLogJetTailReadout
  rw [(canonicalCompletedC3EnrichedTfvdTransport_components s).2.1]
  ring

theorem canonicalCompletedC3EnrichedTfvdLogJetTailReadout_eq_neg_deriv
    {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    canonicalCompletedC3EnrichedTfvdLogJetTailReadout s =
      -deriv canonicalCompletedC3EnrichedTfvdValueTailReadout s := by
  rw [(hasDerivAt_canonicalCompletedC3EnrichedTfvdValueTailReadout hs).deriv]
  ring

def canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
    (z : ℂ) : ℂ :=
  canonicalCompletedC3EnrichedTfvdValueTailReadout
      (operatorHeightParameter z) /
    cpChartFactor 3 (operatorHeightParameter z)

def canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout
    (z : ℂ) : ℂ :=
  let s := operatorHeightParameter z
  Complex.I *
    ((canonicalCompletedC3EnrichedTfvdLogJetTailReadout s *
          cpChartFactor 3 s +
        canonicalCompletedC3EnrichedTfvdValueTailReadout s *
          deriv (cpChartFactor 3) s) /
      cpChartFactor 3 s ^ 2)

theorem hasDerivAt_operatorHeightParameter (z : ℂ) :
    HasDerivAt operatorHeightParameter Complex.I z := by
  change HasDerivAt
    ((fun _ : ℂ => (1 / 2 : ℂ)) + fun y : ℂ => Complex.I * y)
    Complex.I z
  simpa only [id_eq, zero_add, mul_one] using
    (hasDerivAt_const (x := z) (c := (1 / 2 : ℂ))).add
      ((hasDerivAt_id z).const_mul Complex.I)

theorem hasDerivAt_canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    HasDerivAt canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
      (-canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z) z := by
  let s := operatorHeightParameter z
  have hsHalf : s ∈ bracketHalfPlane := by
    change -1 < s.re
    linarith [hs.1]
  have hvalue :=
    hasDerivAt_canonicalCompletedC3EnrichedTfvdValueTailReadout hsHalf
  have hfactorDiff : DifferentiableAt ℂ (cpChartFactor 3) s :=
    (differentiable_cpChartFactor 3 (by norm_num)).differentiableAt
  have hfactor : HasDerivAt (cpChartFactor 3)
      (deriv (cpChartFactor 3) s) s :=
    hfactorDiff.hasDerivAt
  have hfactorNe : cpChartFactor 3 s ≠ 0 :=
    cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hs
  have hquotient := hvalue.div hfactor hfactorNe
  have hcomposed := hquotient.comp z (hasDerivAt_operatorHeightParameter z)
  change HasDerivAt
    (fun w : ℂ =>
      canonicalCompletedC3EnrichedTfvdValueTailReadout
          (operatorHeightParameter w) /
        cpChartFactor 3 (operatorHeightParameter w))
    (-canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z) z
  refine hcomposed.congr_deriv ?_
  unfold canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout
  dsimp only [s]
  ring

theorem canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_neg_deriv
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z =
      -deriv canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z := by
  rw [(hasDerivAt_canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
    hs).deriv]
  ring

def canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
    (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z *
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z

def canonicalCompletedC3EnrichedTfvdBoundaryCompanion
    (z : ℂ) : ℂ :=
  productBoundaryCompanion
    nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z

theorem hasDerivAt_canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    HasDerivAt
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
      (-canonicalCompletedC3EnrichedTfvdBoundaryCompanion z) z := by
  have hxiDiff := nativeXiCompletionFactor_differentiableAt hs
  have hxi : HasDerivAt nativeXiCompletionFactor
      (-nativeXiCompletionBoundaryCompanion z) z := by
    refine hxiDiff.hasDerivAt.congr_deriv ?_
    unfold nativeXiCompletionBoundaryCompanion
    ring
  have hnormalized :=
    hasDerivAt_canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout hs
  have hproduct := hxi.mul hnormalized
  change HasDerivAt
    (fun w : ℂ => nativeXiCompletionFactor w *
      canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout w)
    (-canonicalCompletedC3EnrichedTfvdBoundaryCompanion z) z
  refine hproduct.congr_deriv ?_
  unfold canonicalCompletedC3EnrichedTfvdBoundaryCompanion
    productBoundaryCompanion
  ring

theorem canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_neg_deriv
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion z =
      -deriv
        canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z := by
  rw [(hasDerivAt_canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
    hs).deriv]
  ring

theorem canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z =
      nativeHeightScalar z := by
  have hfactor : cpChartFactor 3 (operatorHeightParameter z) ≠ 0 :=
    cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hs
  unfold canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
    canonicalCompletedC3EnrichedTfvdValueTailReadout nativeHeightScalar
  rw [canonicalCompletedC3EnrichedTfvdTailReadout_eq_nativeScalar hs]
  exact div_eq_iff hfactor |>.2 (by ring)

theorem canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z =
      completedNativeOperatorCharacteristic z := by
  unfold canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
    completedNativeOperatorCharacteristic
  rw [canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
    hs]
  rfl

theorem canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion z =
      completedNativeOperatorBoundaryCompanion z := by
  have hstripNhd :
      {w : ℂ | operatorHeightParameter w ∈ genuineCriticalStrip} ∈ 𝓝 z :=
    (hasDerivAt_operatorHeightParameter z).continuousAt.preimage_mem_nhds
      (isOpen_genuineCriticalStrip.mem_nhds hs)
  have heventual :
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout =ᶠ[𝓝 z]
        completedNativeOperatorCharacteristic := by
    filter_upwards [hstripNhd] with w hw
    exact
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
        hw
  calc
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion z =
        -deriv
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z :=
      canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_neg_deriv hs
    _ = -deriv completedNativeOperatorCharacteristic z := by
      rw [heventual.deriv_eq]
    _ = completedNativeOperatorBoundaryCompanion z := by
      rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]

end

end CarrySelfAdjointOperator

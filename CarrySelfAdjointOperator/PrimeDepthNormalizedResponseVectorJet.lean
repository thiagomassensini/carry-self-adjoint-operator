import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence
import CarrySelfAdjointOperator.CompletedNativeExpandedStructuralBlockProbe
import CarrySelfAdjointOperator.CompletedC3SymplecticCrossingTangentAudit

/-!
# Source-preserving normalized vector jets

The existing four structural channels are retained as a finite Hilbert family.
Normalization is multiplication of those vectors by a fixed geometric scalar
germ, before taking jets. Its finite coefficient transform is linear in the
raw vector tower, with the canonical normalizer held fixed. It is not jointly
linear in arbitrary numerators and denominators. No target moment defines a
vector, metric or coefficient of that transform.
-/

namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter
noncomputable section
set_option maxHeartbeats 200000

abbrev CompletedPrimeDepthJetCarrier :=
  WithLp 2 (CanonicalCompletedC3StructuralChannel →
    CanonicalCompletedC3FullWronskianOperatorCarrier)

private theorem analytic_trace {F P : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hP : AnalyticAt ℂ P 0) :
    AnalyticAt ℂ (completedScalarBoundaryTraceState F P) 0 := by
  unfold completedScalarBoundaryTraceState
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap.analyticAt _ |>.comp
    (hP.prod hF)

/-- The already existing analytic spelling of the completed carrier is
analytic in every order, not merely differentiable once. -/
theorem completedPrimeDepthRawAnalyticState_analyticAt :
    AnalyticAt ℂ canonicalCompletedC3FullWronskianAnalyticState 0 := by
  have hA := nativeXiCompletionFactor_analyticAt_zero
  have hG := nativeHeightScalar_analyticAt_zero
  have hC := canonicalC3ChartFactorHeight_analyticAt_zero
  have hAP : AnalyticAt ℂ nativeXiCompletionBoundaryCompanion 0 := hA.deriv.neg
  have hGP : AnalyticAt ℂ nativeHeightScalarBoundaryCompanion 0 := hG.deriv.neg
  have hCP : AnalyticAt ℂ canonicalC3ChartFactorHeightCompanion 0 :=
    hC.deriv.neg.congr (Eventually.of_forall fun z =>
      (canonicalC3ChartFactorHeightCompanion_eq_neg_deriv z).symm)
  have hRaw : AnalyticAt ℂ canonicalCompletedC3RawAnalyticValue 0 := hC.mul hG
  have hRawP : AnalyticAt ℂ canonicalCompletedC3RawAnalyticCompanion 0 := by
    unfold canonicalCompletedC3RawAnalyticCompanion productBoundaryCompanion
    exact (hCP.mul hG).add (hC.mul hGP)
  have hRawTrace := analytic_trace hRaw hRawP
  have hNativeTrace := analytic_trace hA hAP
  have hChartTrace := analytic_trace hC hCP
  have hArch : AnalyticAt ℂ
      (fun z => WithLp.toLp 2
        ((nativeHeightScalar z * canonicalC3ChartFactorHeight z) •
          completedScalarBoundaryTraceState nativeXiCompletionFactor
            nativeXiCompletionBoundaryCompanion z,
         (nativeHeightScalar z * nativeXiCompletionFactor z) •
          completedScalarBoundaryTraceState canonicalC3ChartFactorHeight
            canonicalC3ChartFactorHeightCompanion z)) 0 :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ CompletedScalarBoundaryTraceCarrier
      CompletedScalarBoundaryTraceCarrier).symm.toContinuousLinearMap.analyticAt _ |>.comp
        (((hG.mul hC).smul hNativeTrace).prod ((hG.mul hA).smul hChartTrace))
  unfold canonicalCompletedC3FullWronskianAnalyticState
  dsimp only
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ CompletedScalarBoundaryTraceCarrier
    CanonicalCompletedC3ArchimedeanChartOperatorCarrier).symm.toContinuousLinearMap.analyticAt _ |>.comp
      ((hA.smul hRawTrace).prod hArch)

/-- All-order regularity of the actual completed TFVD trace projection. -/
theorem completedPrimeDepthRawState_analyticAt (M : ℕ) :
    AnalyticAt ℂ (canonicalCompletedC3FullWronskianOperatorState M) 0 := by
  have hdomain : completedNativeHeightDomain ∈ nhds (0 : ℂ) :=
    isOpen_completedNativeHeightDomain.mem_nhds zero_mem_completedNativeHeightDomain
  apply completedPrimeDepthRawAnalyticState_analyticAt.congr
  filter_upwards [hdomain] with z hz
  exact (canonicalCompletedC3FullWronskianOperatorState_eq_analyticState M hz).symm

private def completionProjection :
    CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ]
      CanonicalCompletedC3FullWronskianOperatorCarrier :=
  let out := (WithLp.prodContinuousLinearEquiv 2 ℂ CompletedScalarBoundaryTraceCarrier
    CanonicalCompletedC3ArchimedeanChartOperatorCarrier).symm.toContinuousLinearMap
  let arch := (WithLp.prodContinuousLinearEquiv 2 ℂ CompletedScalarBoundaryTraceCarrier
    CompletedScalarBoundaryTraceCarrier).symm.toContinuousLinearMap
  let get := (WithLp.fstL 2 ℂ CompletedScalarBoundaryTraceCarrier
    CompletedScalarBoundaryTraceCarrier).comp
      (WithLp.sndL 2 ℂ CompletedScalarBoundaryTraceCarrier
        CanonicalCompletedC3ArchimedeanChartOperatorCarrier)
  out.comp ((0 : CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ] CompletedScalarBoundaryTraceCarrier).prod (arch.comp (get.prod 0)))

private def chartProjection :
    CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ]
      CanonicalCompletedC3FullWronskianOperatorCarrier :=
  let out := (WithLp.prodContinuousLinearEquiv 2 ℂ CompletedScalarBoundaryTraceCarrier
    CanonicalCompletedC3ArchimedeanChartOperatorCarrier).symm.toContinuousLinearMap
  let arch := (WithLp.prodContinuousLinearEquiv 2 ℂ CompletedScalarBoundaryTraceCarrier
    CompletedScalarBoundaryTraceCarrier).symm.toContinuousLinearMap
  let get := (WithLp.sndL 2 ℂ CompletedScalarBoundaryTraceCarrier
    CompletedScalarBoundaryTraceCarrier).comp
      (WithLp.sndL 2 ℂ CompletedScalarBoundaryTraceCarrier
        CanonicalCompletedC3ArchimedeanChartOperatorCarrier)
  out.comp ((0 : CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ] CompletedScalarBoundaryTraceCarrier).prod (arch.comp ((0 : CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ] CompletedScalarBoundaryTraceCarrier).prod get)))

/-- The four existing geometric sectors support holomorphic jets. Head and
tail remain separate; the tail regularity follows from exact synthesis. -/
theorem completedPrimeDepthStructuralState_analyticAt
    (M : ℕ) (role : CanonicalCompletedC3StructuralChannel) :
    AnalyticAt ℂ (canonicalCompletedC3FullWronskianStructuralState M role) 0 := by
  have hFull := completedPrimeDepthRawState_analyticAt M
  have hArch : AnalyticAt ℂ
      (canonicalCompletedC3FullWronskianStructuralState M .xiCompletion) 0 := by
    have heq : canonicalCompletedC3FullWronskianStructuralState M .xiCompletion =
        completionProjection ∘ canonicalCompletedC3FullWronskianOperatorState M := by
      rfl
    rw [heq]
    exact (completionProjection.analyticAt _).comp hFull
  have hChart : AnalyticAt ℂ
      (canonicalCompletedC3FullWronskianStructuralState M .chartCorrection) 0 := by
    have heq : canonicalCompletedC3FullWronskianStructuralState M .chartCorrection =
        chartProjection ∘ canonicalCompletedC3FullWronskianOperatorState M := by
      rfl
    rw [heq]
    exact (chartProjection.analyticAt _).comp hFull
  have hHead : AnalyticAt ℂ
      (canonicalCompletedC3FullWronskianStructuralState M .head) 0 := by
    have hFinite : Differentiable ℂ (finiteBracketedDirichletChart 3 M) :=
      fun s => (hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet M s).differentiableAt
    have hParameter : AnalyticAt ℂ operatorHeightParameter 0 := by
      unfold operatorHeightParameter
      fun_prop
    have hV := (hFinite.analyticAt (operatorHeightParameter 0)).comp hParameter
    have hL : AnalyticAt ℂ (finiteCanonicalLogBracketChart M)
        (operatorHeightParameter 0) :=
      (hFinite.analyticAt (operatorHeightParameter 0)).deriv.neg.congr
        (Eventually.of_forall fun s =>
          (finiteCanonicalLogBracketChart_eq_neg_deriv_valueChart M s).symm)
    have hPair : AnalyticAt ℂ
        (fun z => WithLp.toLp 2
          (Complex.I * finiteCanonicalLogBracketChart M (operatorHeightParameter z),
           finiteBracketedDirichletChart 3 M (operatorHeightParameter z))) 0 :=
      (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap.analyticAt _ |>.comp
        ((analyticAt_const.mul (hL.comp hParameter)).prod hV)
    change AnalyticAt ℂ (fun z => WithLp.toLp 2
      (nativeXiCompletionFactor z •
        WithLp.toLp 2
          (Complex.I * finiteCanonicalLogBracketChart M (operatorHeightParameter z),
           finiteBracketedDirichletChart 3 M (operatorHeightParameter z)), 0)) 0
    exact (WithLp.prodContinuousLinearEquiv 2 ℂ CompletedScalarBoundaryTraceCarrier
      CanonicalCompletedC3ArchimedeanChartOperatorCarrier).symm.toContinuousLinearMap.analyticAt _ |>.comp
        ((nativeXiCompletionFactor_analyticAt_zero.smul hPair).prod analyticAt_const)
  cases role
  · exact hHead
  · apply ((hFull.sub hHead).sub hArch |>.sub hChart).congr
    apply Eventually.of_forall
    intro z
    have h := canonicalCompletedC3FullWronskianStructuralState_synthesis M z
    unfold canonicalCompletedC3StructuralSynthesis at h
    change canonicalCompletedC3FullWronskianOperatorState M z -
      canonicalCompletedC3FullWronskianStructuralState M .head z -
      canonicalCompletedC3FullWronskianStructuralState M .xiCompletion z -
      canonicalCompletedC3FullWronskianStructuralState M .chartCorrection z = _
    rw [← h]
    abel
  · exact hArch
  · exact hChart

/-- Normalization is the prescribed chart and characteristic division, not
an adjustable scalar. It is fixed for all input jet orders. -/
def primeDepthVectorNormalizer (z : ℂ) : ℂ :=
  (canonicalC3ChartFactorHeight z * completedNativeOperatorCharacteristic z)⁻¹

theorem primeDepthVectorNormalizer_analyticAt :
    AnalyticAt ℂ primeDepthVectorNormalizer 0 :=
  (canonicalC3ChartFactorHeight_analyticAt_zero.mul
    (completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain)).inv
      (mul_ne_zero
        (canonicalC3ChartFactorHeight_ne_zero zero_mem_completedNativeHeightDomain)
        completedNativeOperatorCharacteristic_zero_ne_zero)

/-- Normalize the complete geometric sector vectors, retaining their labels. -/
def primeDepthNormalizedStructuralState
    (role : CanonicalCompletedC3StructuralChannel) (z : ℂ) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  primeDepthVectorNormalizer z • canonicalCompletedC3FullWronskianStructuralState 1 role z

theorem primeDepthNormalizedStructuralState_analyticAt
    (role : CanonicalCompletedC3StructuralChannel) :
    AnalyticAt ℂ (primeDepthNormalizedStructuralState role) 0 :=
  primeDepthVectorNormalizer_analyticAt.smul (completedPrimeDepthStructuralState_analyticAt 1 role)

/-- Center-pinned source readout. The center and symplectic rotation are
existing geometric data; the scale is exactly the response normalization. -/
def primeDepthVectorSectorReadout :
    CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ] ℂ :=
  ((2 * (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0))⁻¹) •
    ((innerSL ℂ (canonicalCompletedC3NormalizedFullWronskianOperatorState 1 0) :
      CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ] ℂ).comp
      canonicalCompletedC3FullWronskianOperator)

/-- Fixed linear synthesis/readout of the four retained vector sectors. -/
def primeDepthNormalizedResponseVectorReadout : CompletedPrimeDepthJetCarrier →L[ℂ] ℂ :=
  (∑ role : CanonicalCompletedC3StructuralChannel,
    primeDepthVectorSectorReadout.comp (ContinuousLinearMap.proj role)).comp
      (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : CanonicalCompletedC3StructuralChannel =>
          CanonicalCompletedC3FullWronskianOperatorCarrier)).toContinuousLinearMap

theorem primeDepthNormalizedResponseVectorReadout_apply (x : CompletedPrimeDepthJetCarrier) :
    primeDepthNormalizedResponseVectorReadout x =
      ∑ role, primeDepthVectorSectorReadout ((WithLp.ofLp x) role) := by
  simp [primeDepthNormalizedResponseVectorReadout]

/-- The fixed readout of normalized sectors is the existing full response,
before any Taylor coefficient or moment is mentioned. -/
theorem primeDepthNormalizedStructuralState_readout (z : ℂ) :
    (∑ role, primeDepthVectorSectorReadout (primeDepthNormalizedStructuralState role z)) =
      canonicalCompletedC3FullOperatorNormalizedResponse 1 z := by
  simp only [primeDepthNormalizedStructuralState, ← map_sum, ← Finset.smul_sum,
    sum_canonicalCompletedC3StructuralChannel_eq_synthesis,
    canonicalCompletedC3FullWronskianStructuralState_synthesis]
  change (2 * (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0))⁻¹ *
    inner ℂ (canonicalCompletedC3NormalizedFullWronskianOperatorState 1 0)
      (canonicalCompletedC3FullWronskianOperator
        (primeDepthVectorNormalizer z • canonicalCompletedC3FullWronskianOperatorState 1 z)) =
    inner ℂ (canonicalCompletedC3NormalizedFullWronskianOperatorState 1 0)
      (canonicalCompletedC3FullWronskianOperator
        ((canonicalC3ChartFactorHeight z)⁻¹ • canonicalCompletedC3FullWronskianOperatorState 1 z)) /
      (2 * completedNativeOperatorCharacteristic z *
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0))
  rw [map_smul, inner_smul_right, map_smul, inner_smul_right]
  simp only [primeDepthVectorNormalizer, mul_inv_rev, div_eq_mul_inv]
  ring

private theorem readout_taylorJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (L : E →L[ℂ] ℂ) {f : ℂ → E} (hf : AnalyticAt ℂ f 0) (r : ℕ) :
    L (completedGreenTaylorJet f r) =
      iteratedDeriv r (L ∘ f) 0 / (r.factorial : ℂ) := by
  have hd := L.iteratedFDeriv_comp_left (hf.contDiffAt : ContDiffAt ℂ (r : ℕ) f 0)
    (i := r) le_rfl
  have he := congrArg (fun p => p (fun _ : Fin r => (1 : ℂ))) hd
  have he' : iteratedDeriv r (L ∘ f) 0 = L (iteratedDeriv r f 0) := he
  rw [completedGreenTaylorJet, map_smul, ← he']
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- Vector Leibniz rule with factorial normalization. This is linear in the
vector jet tower after the scalar germ has been fixed. -/
theorem completedPrimeDepthTaylorJet_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {d : ℂ → ℂ} {f : ℂ → E}
    (hd : AnalyticAt ℂ d 0) (hf : AnalyticAt ℂ f 0) (r : ℕ) :
    completedGreenTaylorJet (fun z => d z • f z) r =
      ∑ j ∈ Finset.range (r + 1),
        (iteratedDeriv j d 0 / (j.factorial : ℂ)) •
          completedGreenTaylorJet f (r - j) := by
  have hl := iteratedDerivWithin_smul (Set.mem_univ (0 : ℂ)) uniqueDiffOn_univ
    (hd.contDiffAt.contDiffWithinAt : ContDiffWithinAt ℂ (r : ℕ) d Set.univ 0)
    (hf.contDiffAt.contDiffWithinAt : ContDiffWithinAt ℂ (r : ℕ) f Set.univ 0)
  simp only [iteratedDerivWithin_univ] at hl
  change iteratedDeriv r (fun z => d z • f z) 0 = _ at hl
  unfold completedGreenTaylorJet
  rw [hl, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfact : (r.choose j : ℂ) * (j.factorial : ℂ) * ((r - j).factorial : ℂ) =
      (r.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjr
  have hcoeff : (r.factorial : ℂ)⁻¹ * (r.choose j : ℂ) * iteratedDeriv j d 0 =
      (iteratedDeriv j d 0 / (j.factorial : ℂ)) * ((r - j).factorial : ℂ)⁻¹ := by
    have hr : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
    have hj0 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hsub : ((r - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    linear_combination (iteratedDeriv j d 0) * hfact
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_smul, ← mul_assoc]
  rw [hcoeff]

/-- The prescribed full scalar normalizer, in factorial-normalized orders. -/
def primeDepthVectorNormalizerCoefficient (r : ℕ) : ℂ :=
  iteratedDeriv r primeDepthVectorNormalizer 0 / (r.factorial : ℂ)

/-- Finite lower-triangular convolution. The coefficients are fixed by chart
and completion; input vector towers remain arbitrary. -/
def primeDepthNormalizedJetTransform (N : ℕ) :
    (Fin N → CanonicalCompletedC3FullWronskianOperatorCarrier) →ₗ[ℂ]
      (Fin N → CanonicalCompletedC3FullWronskianOperatorCarrier) where
  toFun raw i := ∑ j ∈ Finset.range (i.val + 1),
    primeDepthVectorNormalizerCoefficient j • raw ⟨i.val - j, by omega⟩
  map_add' := by
    intros
    ext i
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' := by
    intros
    ext i
    simp [Finset.smul_sum, smul_smul, mul_comm]

/-- Every finite transformed tower is the actual normalized vector-jet
prefix. No scalar quotient is declared linear in a varying denominator. -/
theorem primeDepthNormalizedJetTransform_eq_jets (N : ℕ)
    (role : CanonicalCompletedC3StructuralChannel) :
    primeDepthNormalizedJetTransform N
      (fun i => completedGreenTaylorJet
        (canonicalCompletedC3FullWronskianStructuralState 1 role) i.val) =
      fun i => completedGreenTaylorJet (primeDepthNormalizedStructuralState role) i.val := by
  ext i
  exact (completedPrimeDepthTaylorJet_smul primeDepthVectorNormalizer_analyticAt
    (completedPrimeDepthStructuralState_analyticAt 1 role) i.val).symm

/-- Increasing a cutoff leaves all previously computed normalized jets
unchanged. -/
theorem primeDepthNormalizedJetTransform_prefix (N : ℕ)
    (raw : Fin (N + 1) → CanonicalCompletedC3FullWronskianOperatorCarrier)
    (i : Fin N) :
    primeDepthNormalizedJetTransform (N + 1) raw i.castSucc =
      primeDepthNormalizedJetTransform N (fun j => raw j.castSucc) i := by
  rfl

/-- The odd normalized jets of the four geometric sectors. The definition
mentions neither geometric moments nor their canonical identification. -/
def primeDepthNormalizedResponseVectorJet (n : ℕ) : CompletedPrimeDepthJetCarrier :=
  WithLp.toLp 2 (fun role =>
    completedGreenTaylorJet (primeDepthNormalizedStructuralState role) (2 * n + 1))

private theorem vectorJet_readout_source (n : ℕ) :
    primeDepthNormalizedResponseVectorReadout (primeDepthNormalizedResponseVectorJet n) =
      primeDepthCompletedNativeResponseTaylorCoefficient (2 * n + 1) := by
  let r := 2 * n + 1
  rw [primeDepthNormalizedResponseVectorReadout_apply]
  change (∑ role, primeDepthVectorSectorReadout
    (completedGreenTaylorJet (primeDepthNormalizedStructuralState role) r)) = _
  simp_rw [readout_taylorJet primeDepthVectorSectorReadout
    (primeDepthNormalizedStructuralState_analyticAt _)]
  rw [← Finset.sum_div]
  have hsum := iteratedDeriv_fun_sum (n := r)
    (f := fun role => primeDepthVectorSectorReadout ∘ primeDepthNormalizedStructuralState role)
    (x := (0 : ℂ)) (I := Finset.univ)
    (fun role _ => ((primeDepthVectorSectorReadout.analyticAt _).comp
      (primeDepthNormalizedStructuralState_analyticAt role)).contDiffAt)
  rw [← hsum]
  have heq : (fun z => ∑ role, primeDepthVectorSectorReadout
        (primeDepthNormalizedStructuralState role z)) =
      canonicalCompletedC3FullOperatorNormalizedResponse 1 :=
    funext primeDepthNormalizedStructuralState_readout
  change iteratedDeriv r
    (fun z => ∑ role, primeDepthVectorSectorReadout (primeDepthNormalizedStructuralState role z)) 0 /
    (r.factorial : ℂ) = _
  rw [heq]
  have hgerm := (canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed 1).trans
    primeDepthCompletedNativeNormalizedResponse_eventuallyEq_completed.symm
  rw [hgerm.iteratedDeriv_eq r]
  rfl

/-- Each all-order vector is also the indicated row of a coherent finite
triangular transform of the raw geometric jets. -/
theorem primeDepthNormalizedResponseVectorJet_eq_finiteTransform (n : ℕ) :
    primeDepthNormalizedResponseVectorJet n = WithLp.toLp 2 (fun role =>
      primeDepthNormalizedJetTransform (2 * n + 2)
        (fun i => completedGreenTaylorJet
          (canonicalCompletedC3FullWronskianStructuralState 1 role) i.val)
        ⟨2 * n + 1, by omega⟩) := by
  apply WithLp.ofLp_injective
  change (fun role => completedGreenTaylorJet (primeDepthNormalizedStructuralState role)
    (2 * n + 1)) = _
  funext role
  exact (congrFun (primeDepthNormalizedJetTransform_eq_jets (2 * n + 2) role)
    ⟨2 * n + 1, by omega⟩).symm

/-- Source-first order-zero canary. -/
theorem primeDepthNormalizedResponseVectorJet_readout_zero :
    primeDepthNormalizedResponseVectorReadout (primeDepthNormalizedResponseVectorJet 0) =
      (primeDepthGeometricMoment 0 : ℂ) :=
  (vectorJet_readout_source 0).trans (primeDepthGeometricMoment_coe 0).symm

/-- Source-first order-one canary. -/
theorem primeDepthNormalizedResponseVectorJet_readout_one :
    primeDepthNormalizedResponseVectorReadout (primeDepthNormalizedResponseVectorJet 1) =
      (primeDepthGeometricMoment 1 : ℂ) :=
  (vectorJet_readout_source 1).trans (primeDepthGeometricMoment_coe 1).symm

/-- Source-first order-two canary. -/
theorem primeDepthNormalizedResponseVectorJet_readout_two :
    primeDepthNormalizedResponseVectorReadout (primeDepthNormalizedResponseVectorJet 2) =
      (primeDepthGeometricMoment 2 : ℂ) :=
  (vectorJet_readout_source 2).trans (primeDepthGeometricMoment_coe 2).symm

/-- All-order vector lift with one fixed continuous linear readout. -/
theorem primeDepthNormalizedResponseVectorJet_readout (n : ℕ) :
    primeDepthNormalizedResponseVectorReadout (primeDepthNormalizedResponseVectorJet n) =
      (primeDepthGeometricMoment n : ℂ) :=
  (vectorJet_readout_source n).trans (primeDepthGeometricMoment_coe n).symm

/-- Only after the source-first vector lift: identification with the canonical
sequence by the already proved uniqueness theorem. -/
theorem primeDepthNormalizedResponseVectorJet_readout_canonical (n : ℕ) :
    primeDepthNormalizedResponseVectorReadout (primeDepthNormalizedResponseVectorJet n) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  rw [primeDepthNormalizedResponseVectorJet_readout,
    primeDepthGeometricMoment_eq_canonical]

end
end CarrySelfAdjointOperator

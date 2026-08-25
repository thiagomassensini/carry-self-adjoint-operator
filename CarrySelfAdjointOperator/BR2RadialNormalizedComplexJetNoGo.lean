import CarrySelfAdjointOperator.BR2CompletedGreenJetTransportObstruction
import CarrySelfAdjointOperator.CompletedGreenDiagonalClosure
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# No-go for complex Taylor jets after radial phase normalization

The completed C3 scalar seam and its enriched final readout are exact.  This
file addresses a different issue: the BR2 all-order transport abbreviation
currently targets complex Taylor derivatives of a state to which the radial
phase has already been applied.

One retained C3 coordinate factors locally as a nonzero holomorphic function
times `exp (log 3 * im z)`.  The latter is real differentiable but not complex
differentiable at the Taylor center.  Hence the normalized product state is
not complex differentiable there, independently of the chosen archimedean
Hilbert carrier.  Since Lean's first complex `iteratedDeriv` is zero at a
nondifferentiable point, a supported injective incidence transport into those
complex parity jets cannot exist.

This does not obstruct the concrete projective TFVD Hilbert transport or a
real-axis/raw-holomorphic jet construction.  It formalizes the channel-order
guardrail: radial phase rotation belongs at the final readout, after the
all-order carrier has been retained.
-/

namespace CarrySelfAdjointOperator

noncomputable section

def br2RadialExponent (z : ℂ) : ℝ :=
  ((Real.log 3) • Complex.imCLM) z

def br2RadialPhase (z : ℂ) : ℂ :=
  Complex.ofRealCLM (Real.exp (br2RadialExponent z))

def br2RadialPhaseFDeriv : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.toSpanSingleton ℝ
        (Real.exp (br2RadialExponent 0))).comp
      ((Real.log 3) • Complex.imCLM))

theorem br2RadialPhase_hasFDerivAt :
    HasFDerivAt br2RadialPhase br2RadialPhaseFDeriv 0 := by
  have him : HasFDerivAt br2RadialExponent
      ((Real.log 3) • Complex.imCLM) 0 := by
    exact ((Real.log 3) • Complex.imCLM).hasFDerivAt
  have hexp : HasFDerivAt
      (fun z : ℂ => Real.exp (br2RadialExponent z))
      ((ContinuousLinearMap.toSpanSingleton ℝ
          (Real.exp (br2RadialExponent 0))).comp
        ((Real.log 3) • Complex.imCLM)) 0 := by
    exact (Real.hasDerivAt_exp (br2RadialExponent 0)).hasFDerivAt.comp 0 him
  exact Complex.ofRealCLM.hasFDerivAt.comp 0 hexp

theorem br2RadialPhase_not_differentiableAt_complex :
    ¬ DifferentiableAt ℂ br2RadialPhase 0 := by
  intro hcomplex
  have hcr :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hcomplex).2
  rw [br2RadialPhase_hasFDerivAt.fderiv] at hcr
  have hI : br2RadialPhaseFDeriv Complex.I = (Real.log 3 : ℂ) := by
    simp [br2RadialPhaseFDeriv, br2RadialExponent]
  have hOne : br2RadialPhaseFDeriv 1 = 0 := by
    simp [br2RadialPhaseFDeriv, br2RadialExponent]
  rw [hI, hOne, smul_zero] at hcr
  have hlog : Real.log 3 = 0 := Complex.ofReal_injective hcr
  exact (ne_of_gt (Real.log_pos (by norm_num))) hlog

abbrev CanonicalC3FirstLeg := WithLp 2 (Fin 3 → ℂ)

def canonicalCompletedC3FirstZeroReadout :
    CanonicalCompletedC3HilbertCarrier →L[ℂ] ℂ :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℂ) 0).comp
    (WithLp.fstL 2 ℂ CanonicalC3FirstLeg CanonicalC3FirstLeg)

def completedNativeC3FirstZeroReadout
    (Hxi : Type*) [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi] :
    BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier →L[ℂ] ℂ :=
  canonicalCompletedC3FirstZeroReadout.comp
    (WithLp.sndL 2 ℂ Hxi CanonicalCompletedC3HilbertCarrier)

@[simp] theorem canonicalCompletedC3FirstZeroReadout_state (z : ℂ) :
    canonicalCompletedC3FirstZeroReadout
        (canonicalCompletedOperatorC3HilbertState z) =
      CPFormal.Analytic.Cp.phaseNormalizedCpGenuineGreenGradient 3
        (operatorHeightParameter z) 0 := by
  unfold canonicalCompletedC3FirstZeroReadout
    canonicalCompletedOperatorC3HilbertState canonicalCompletedOperatorC3State
  rw [canonicalEnrichedC3SourcePort_eq_greenBoundaryPair]
  rfl

@[simp] theorem completedNativeC3FirstZeroReadout_normalizedState
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (z : ℂ) :
    completedNativeC3FirstZeroReadout Hxi
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) z) =
      (((Real.sqrt 2 : ℝ) : ℂ) *
          completedNativeOperatorCharacteristic z)⁻¹ *
        (nativeXiCompletionFactor z *
          CPFormal.Analytic.Cp.phaseNormalizedCpGenuineGreenGradient 3
            (operatorHeightParameter z) 0) := by
  unfold normalizedCompletedGreenState completedNativeC3FirstZeroReadout
  rw [map_smul]
  change
    (((Real.sqrt 2 : ℝ) : ℂ) *
          completedNativeOperatorCharacteristic z)⁻¹ *
        canonicalCompletedC3FirstZeroReadout
          ((WithLp.ofLp
            (completedNativeC3ProductLedgerState xiState z)).2) = _
  rw [completedNativeC3ProductLedgerState_snd, map_smul,
    canonicalCompletedC3FirstZeroReadout_state]
  rfl

theorem phaseNormalizedC3Gradient_operatorHeight_eq_radialPhase_mul
    (z : ℂ) :
    CPFormal.Analytic.Cp.phaseNormalizedCpGenuineGreenGradient 3
        (operatorHeightParameter z) 0 =
      br2RadialPhase z *
        CPFormal.Analytic.Cp.positiveDirichletGradient
          (operatorHeightParameter z) 0 := by
  rw [CPFormal.Analytic.Cp.phaseNormalizedCpGenuineGreenGradient_eq_phaseNormalizedCpBlockGradient
      3 (by norm_num),
    CPFormal.Analytic.Cp.phaseNormalizedCpBlockGradient_eq_radial_mul
      3 (by norm_num)]
  congr 1
  unfold br2RadialPhase
  change (((3 : ℝ) ^
      (-CPFormal.Analytic.Cp.criticalDisplacement
        (operatorHeightParameter z).re) : ℝ) : ℂ) =
    (Real.exp (br2RadialExponent z) : ℂ)
  norm_cast
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  simp [br2RadialExponent, operatorHeightParameter,
    CPFormal.Analytic.Cp.criticalDisplacement, Complex.mul_re]

def br2C3HolomorphicFactor (z : ℂ) : ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ) * nativeHeightScalar z)⁻¹ *
    CPFormal.Analytic.Cp.positiveDirichletGradient
      (operatorHeightParameter z) 0

theorem nativeHeightScalar_zero_ne_zero :
    nativeHeightScalar 0 ≠ 0 := by
  have h := completedNativeOperatorCharacteristic_zero_ne_zero
  unfold completedNativeOperatorCharacteristic at h
  exact (mul_ne_zero_iff.mp h).2

theorem positiveDirichletGradient_operatorHeight_zero_ne_zero :
    CPFormal.Analytic.Cp.positiveDirichletGradient
        (operatorHeightParameter 0) 0 ≠ 0 := by
  intro hgradient
  have hstrip : operatorHeightParameter 0 ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hedge := CPFormal.Analytic.Cp.finiteReflectedGradientEdge_re_pos
    hstrip 0
  rw [CPFormal.Analytic.Cp.finiteReflectedGradientEdge] at hedge
  rw [hgradient] at hedge
  norm_num at hedge

theorem positiveDirichletGradient_operatorHeight_differentiableAt_zero :
    DifferentiableAt ℂ
      (fun z : ℂ =>
        CPFormal.Analytic.Cp.positiveDirichletGradient
          (operatorHeightParameter z) 0) 0 := by
  have hexponent : DifferentiableAt ℂ
      (fun z : ℂ => -(operatorHeightParameter z)) 0 := by
    unfold operatorHeightParameter
    fun_prop
  unfold CPFormal.Analytic.Cp.positiveDirichletGradient
    CPFormal.Analytic.Cp.natDirichletTerm
    CPFormal.Analytic.Cp.dirichletTerm
  simpa using
    (hexponent.const_cpow (c := (2 : ℂ)) (Or.inl (by norm_num))).sub
      (hexponent.const_cpow (c := (1 : ℂ)) (Or.inl (by norm_num)))

theorem br2C3HolomorphicFactor_differentiableAt :
    DifferentiableAt ℂ br2C3HolomorphicFactor 0 := by
  have hstrip : operatorHeightParameter 0 ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hnativeDomain : operatorHeightParameter 0 ∈
      NativeCarrySpectralWeyl.Camera.nativeScalarDomain :=
    ⟨by linarith [hstrip.1], hstrip.2⟩
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  unfold br2C3HolomorphicFactor
  exact (((differentiableAt_const (c := ((Real.sqrt 2 : ℝ) : ℂ))).mul
      (nativeHeightScalar_differentiableAt hnativeDomain)).inv
        (mul_ne_zero hsqrt nativeHeightScalar_zero_ne_zero)).mul
    positiveDirichletGradient_operatorHeight_differentiableAt_zero

theorem br2C3HolomorphicFactor_zero_ne_zero :
    br2C3HolomorphicFactor 0 ≠ 0 := by
  unfold br2C3HolomorphicFactor
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  exact mul_ne_zero
    (inv_ne_zero (mul_ne_zero hsqrt nativeHeightScalar_zero_ne_zero))
    positiveDirichletGradient_operatorHeight_zero_ne_zero

theorem completedNativeC3FirstZeroReadout_eventuallyEq_radial_mul_holomorphic
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) :
    (fun z : ℂ ↦
        completedNativeC3FirstZeroReadout Hxi
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic
            (completedNativeC3ProductLedgerState xiState) z)) =ᶠ[nhds 0]
      fun z : ℂ ↦ br2RadialPhase z * br2C3HolomorphicFactor z := by
  have hstrip : operatorHeightParameter 0 ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hnativeDomain : operatorHeightParameter 0 ∈
      NativeCarrySpectralWeyl.Camera.nativeScalarDomain :=
    ⟨by linarith [hstrip.1], hstrip.2⟩
  have hxiEventually : ∀ᶠ z in nhds (0 : ℂ),
      nativeXiCompletionFactor z ≠ 0 :=
    (nativeXiCompletionFactor_differentiableAt hstrip).continuousAt.eventually_ne
      (nativeXiCompletionFactor_ne_zero hstrip)
  have hheightEventually : ∀ᶠ z in nhds (0 : ℂ),
      nativeHeightScalar z ≠ 0 :=
    (nativeHeightScalar_differentiableAt hnativeDomain).continuousAt.eventually_ne
      nativeHeightScalar_zero_ne_zero
  filter_upwards [hxiEventually, hheightEventually] with z hxi hheight
  rw [completedNativeC3FirstZeroReadout_normalizedState,
    phaseNormalizedC3Gradient_operatorHeight_eq_radialPhase_mul]
  unfold completedNativeOperatorCharacteristic br2C3HolomorphicFactor
    nativeHeightScalar
  change NativeCarrySpectralWeyl.Camera.nativeScalar
      (operatorHeightParameter z) ≠ 0 at hheight
  field_simp [hxi, hheight]

theorem completedNativeC3FirstZeroReadout_not_differentiableAt_complex
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) :
    ¬ DifferentiableAt ℂ
      (fun z : ℂ ↦
        completedNativeC3FirstZeroReadout Hxi
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic
            (completedNativeC3ProductLedgerState xiState) z)) 0 := by
  intro hreadout
  have heq :=
    completedNativeC3FirstZeroReadout_eventuallyEq_radial_mul_holomorphic xiState
  have hproduct : DifferentiableAt ℂ
      (fun z : ℂ ↦ br2RadialPhase z * br2C3HolomorphicFactor z) 0 := by
    exact hreadout.congr_of_eventuallyEq heq.symm
  have hquotient : DifferentiableAt ℂ
      (fun z : ℂ ↦
        (br2RadialPhase z * br2C3HolomorphicFactor z) /
          br2C3HolomorphicFactor z) 0 :=
    hproduct.div br2C3HolomorphicFactor_differentiableAt
      br2C3HolomorphicFactor_zero_ne_zero
  have hfactorEventually : ∀ᶠ z in nhds (0 : ℂ),
      br2C3HolomorphicFactor z ≠ 0 :=
    br2C3HolomorphicFactor_differentiableAt.continuousAt.eventually_ne
      br2C3HolomorphicFactor_zero_ne_zero
  have hradial : DifferentiableAt ℂ br2RadialPhase 0 := by
    apply hquotient.congr_of_eventuallyEq
    filter_upwards [hfactorEventually] with z hz
    exact (mul_div_cancel_right₀ (br2RadialPhase z) hz).symm
  exact br2RadialPhase_not_differentiableAt_complex hradial

theorem normalizedCompletedNativeC3ProductLedger_not_differentiableAt_zero
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) :
    ¬ DifferentiableAt ℂ
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        (completedNativeC3ProductLedgerState xiState)) 0 := by
  intro hstate
  have hreadout : DifferentiableAt ℂ
      (fun z : ℂ ↦
        completedNativeC3FirstZeroReadout Hxi
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic
            (completedNativeC3ProductLedgerState xiState) z)) 0 :=
    (completedNativeC3FirstZeroReadout Hxi).differentiableAt.comp 0 hstate
  exact completedNativeC3FirstZeroReadout_not_differentiableAt_complex
    xiState hreadout

theorem not_nonempty_canonicalCompletedNativeBR2IncidenceJetTransport
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (xiState : ℂ → Hxi) :
    ¬ Nonempty
      (CanonicalCompletedNativeBR2IncidenceJetTransport
        base radius xiState) := by
  rintro ⟨transport⟩
  exact normalizedCompletedNativeC3ProductLedger_not_differentiableAt_zero
    xiState
    (normalizedCompletedNativeC3ProductLedger_differentiableAt_zero_of_incidenceTransport
      hbase hradius xiState transport)

end

end CarrySelfAdjointOperator

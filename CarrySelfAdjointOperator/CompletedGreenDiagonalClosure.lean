import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import CarrySelfAdjointOperator.CanonicalC3GreenIntertwiner
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Diagonal closure of the completed Green kernel

The polarized Green identity determines the normalized point-state kernel
away from collisions as the slope of the scalar response.  On the real
spectral axis the multiplier vanishes at a collision, so the cross-multiplied
identity alone reads `0 = 0` there.

There is nevertheless no independent diagonal datum once the normalized
state is continuous.  The off-diagonal slope tends to the derivative of the
response, while continuity of the state kernel tends to its diagonal norm.
Uniqueness of limits therefore gives the exact removable-singularity law

`inner (normalizedState x) (normalizedState x) = response' x`.

This is the scalar regularity/minimality seam needed by the finite-difference
Gram route.  It uses neither Hilbert-valued differentiation nor a selected
inverse.
-/

namespace CarrySelfAdjointOperator

open Filter Topology
open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Continuity of the unnormalized state and of the nonvanishing scalar
factor passes to the canonical Green normalization. -/
theorem continuousAt_normalizedCompletedGreenState
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ → ℂ} {state : ℂ → E} {x : ℂ}
    (hF : ContinuousAt F x) (hFne : F x ≠ 0)
    (hstate : ContinuousAt state x) :
    ContinuousAt (normalizedCompletedGreenState F state) x := by
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  unfold normalizedCompletedGreenState
  exact ((continuousAt_const.mul hF).inv₀ (mul_ne_zero hsqrt hFne)).smul hstate

/-- An even scalar germ has zero first derivative at its center.  This is
the local parity statement needed to see that its negative logarithmic
derivative response vanishes at the center. -/
theorem deriv_zero_of_eventually_even
    (F : ℂ → ℂ)
    (heven : (fun z ↦ F (-z)) =ᶠ[nhds 0] F) :
    deriv F 0 = 0 := by
  have hderiv := heven.deriv_eq
  rw [deriv_comp_neg] at hderiv
  simp only [neg_zero] at hderiv
  have htwo : (2 : ℂ) * deriv F 0 = 0 := by
    calc
      (2 : ℂ) * deriv F 0 = deriv F 0 - (-deriv F 0) := by ring
      _ = 0 := by rw [hderiv]; ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- For the canonical companion `Psi = -F'`, local evenness forces the
normalized scalar response to vanish at the centered origin. -/
theorem completedGreenNormalizedResponse_zero_of_eventually_even
    {F : ℂ → ℂ}
    (heven : (fun z ↦ F (-z)) =ᶠ[nhds 0] F) :
    completedGreenNormalizedResponse F (fun z ↦ -deriv F z) 0 = 0 := by
  unfold completedGreenNormalizedResponse
  dsimp only
  rw [deriv_zero_of_eventually_even F heven]
  simp

/-- A continuous normalized Green state has no free norm diagonal at a real
spectral point.  The diagonal is forced to be the derivative of the scalar
response by the off-diagonal Green identity.

The hypotheses `hdomain` and `hF` are deliberately local.  They say only that
the Green representation and the normalization are valid in a neighborhood
of the collision point. -/
theorem normalizedCompletedGreenState_inner_self_eq_responseDerivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    {x derivative : ℂ}
    (hgreen : HasDivisionFreeGreenRepresentationOn domain F Psi state)
    (hdomain : domain ∈ nhds x)
    (hF : ∀ᶠ z in nhds x, F z ≠ 0)
    (hxReal : (starRingEnd ℂ) x = x)
    (hresponseReal :
      (starRingEnd ℂ) (completedGreenNormalizedResponse F Psi x) =
        completedGreenNormalizedResponse F Psi x)
    (hstate : ContinuousAt (normalizedCompletedGreenState F state) x)
    (hderiv : HasDerivAt
      (completedGreenNormalizedResponse F Psi) derivative x) :
    inner ℂ
        (normalizedCompletedGreenState F state x)
        (normalizedCompletedGreenState F state x) = derivative := by
  let normalizedState : ℂ → E :=
    normalizedCompletedGreenState F state
  let response : ℂ → ℂ :=
    completedGreenNormalizedResponse F Psi

  have hkernelSlope :
      (fun z ↦ inner ℂ (normalizedState x) (normalizedState z)) =ᶠ[nhdsWithin x {x}ᶜ]
        slope response x := by
    have hdomain' : ∀ᶠ z in nhdsWithin x {x}ᶜ, z ∈ domain :=
      (show ∀ᶠ z in nhds x, z ∈ domain from hdomain).filter_mono
        inf_le_left
    have hF' : ∀ᶠ z in nhdsWithin x {x}ᶜ, F z ≠ 0 :=
      hF.filter_mono inf_le_left
    filter_upwards
      [hdomain', hF', self_mem_nhdsWithin] with z hzDomain hzF hzNe
    have hxDomain : x ∈ domain := mem_of_mem_nhds hdomain
    have hxF : F x ≠ 0 := mem_of_mem_nhds hF
    have hpolarized := normalizedCompletedGreenState_polarizedResponse
      hgreen hzDomain hxDomain hzF hxF
    change
      (z - (starRingEnd ℂ) x) *
          inner ℂ (normalizedState x) (normalizedState z) =
        response z - (starRingEnd ℂ) (response x) at hpolarized
    rw [hxReal, hresponseReal] at hpolarized
    rw [slope_def_module]
    simp only [smul_eq_mul]
    have hzx : z - x ≠ 0 := sub_ne_zero.mpr hzNe
    calc
      inner ℂ (normalizedState x) (normalizedState z) =
          (z - x)⁻¹ * ((z - x) *
            inner ℂ (normalizedState x) (normalizedState z)) := by
              field_simp
      _ = (z - x)⁻¹ * (response z - response x) := by
        rw [hpolarized]

  have hkernelTendsto :
      Tendsto (fun z ↦ inner ℂ (normalizedState x) (normalizedState z))
        (nhdsWithin x {x}ᶜ)
        (nhds (inner ℂ (normalizedState x) (normalizedState x))) := by
    exact Filter.Tendsto.inner tendsto_const_nhds
      (hstate.tendsto.mono_left inf_le_left)

  have hslopeTendsto :
      Tendsto (slope response x) (nhdsWithin x {x}ᶜ) (nhds derivative) := by
    exact hderiv.tendsto_slope

  apply tendsto_nhds_unique hkernelTendsto
  exact hslopeTendsto.congr' hkernelSlope.symm

/-- Centered-origin specialization.  If the response vanishes at the origin,
the two conjugation-fixed hypotheses of the general diagonal theorem are
automatic. -/
theorem normalizedCompletedGreenState_inner_self_zero_eq_responseDerivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    {derivative : ℂ}
    (hgreen : HasDivisionFreeGreenRepresentationOn domain F Psi state)
    (hdomain : domain ∈ nhds 0)
    (hF : ∀ᶠ z in nhds 0, F z ≠ 0)
    (hresponseZero : completedGreenNormalizedResponse F Psi 0 = 0)
    (hstate : ContinuousAt (normalizedCompletedGreenState F state) 0)
    (hderiv : HasDerivAt
      (completedGreenNormalizedResponse F Psi) derivative 0) :
    inner ℂ
        (normalizedCompletedGreenState F state 0)
        (normalizedCompletedGreenState F state 0) = derivative := by
  apply normalizedCompletedGreenState_inner_self_eq_responseDerivative
    hgreen hdomain hF
  · simp
  · simp [hresponseZero]
  · exact hstate
  · exact hderiv

/-! ## Canonical completed-native specialization -/

/-- The centered strip is an open neighborhood of the Taylor center. -/
theorem isOpen_completedNativeHeightDomain :
    IsOpen completedNativeHeightDomain := by
  have hopen : IsOpen genuineCriticalStrip := by
    change IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})
    exact
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
  have hparameter : Continuous operatorHeightParameter := by
    unfold operatorHeightParameter
    fun_prop
  exact hopen.preimage hparameter

/-- The exact centered reflection theorem holds as an equality of germs at
the origin. -/
theorem completedNativeOperatorCharacteristic_eventually_even :
    (fun z ↦ completedNativeOperatorCharacteristic (-z)) =ᶠ[nhds 0]
      completedNativeOperatorCharacteristic := by
  have hdomain : completedNativeHeightDomain ∈ nhds 0 :=
    isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain
  filter_upwards [hdomain] with z hz
  exact completedNativeOperatorCharacteristic_neg hz

/-- Hence the canonical negative-logarithmic-derivative response has no
constant term.  This is obtained from reflection, not inserted as a parity
convention. -/
theorem completedNativeGreenNormalizedResponse_zero :
    completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion 0 = 0 := by
  change completedGreenNormalizedResponse
      completedNativeOperatorCharacteristic
      (fun z ↦ -deriv completedNativeOperatorCharacteristic z) 0 = 0
  exact completedGreenNormalizedResponse_zero_of_eventually_even
    completedNativeOperatorCharacteristic_eventually_even

/-- The completed characteristic is holomorphic, hence continuous, at the
Taylor center. -/
theorem completedNativeOperatorCharacteristic_differentiableAt_zero :
    DifferentiableAt ℂ completedNativeOperatorCharacteristic 0 := by
  have hstrip : operatorHeightParameter 0 ∈ genuineCriticalStrip := by
    simpa [completedNativeHeightDomain] using
      zero_mem_completedNativeHeightDomain
  have hnativeDomain :
      operatorHeightParameter 0 ∈ nativeScalarDomain :=
    ⟨by linarith [hstrip.1], hstrip.2⟩
  change DifferentiableAt ℂ
    (fun z ↦ nativeXiCompletionFactor z * nativeHeightScalar z) 0
  exact (nativeXiCompletionFactor_differentiableAt hstrip).mul
    (nativeHeightScalar_differentiableAt hnativeDomain)

/-- For the concrete completed operator, continuity of the normalized state
removes the diagonal hypothesis altogether: its center norm is exactly the
derivative of the canonical scalar response. -/
theorem completedNativeGreenState_inner_self_zero_eq_responseDerivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {state : ℂ → E} {derivative : ℂ}
    (hgreen : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    (hstate : ContinuousAt
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic state) 0)
    (hderiv : HasDerivAt
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) derivative 0) :
    inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state 0)
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state 0) = derivative := by
  apply normalizedCompletedGreenState_inner_self_zero_eq_responseDerivative
    hgreen
  · exact isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain
  · exact
      completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
        completedNativeOperatorCharacteristic_zero_ne_zero
  · exact completedNativeGreenNormalizedResponse_zero
  · exact hstate
  · exact hderiv

/-- Unnormalized-state version of the same closure.  The normalization is
continuous automatically because the completed characteristic is nonzero at
the center. -/
theorem completedNativeGreenState_inner_self_zero_eq_responseDerivative_of_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {state : ℂ → E} {derivative : ℂ}
    (hgreen : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    (hstate : ContinuousAt state 0)
    (hderiv : HasDerivAt
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) derivative 0) :
    inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state 0)
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state 0) = derivative := by
  apply completedNativeGreenState_inner_self_zero_eq_responseDerivative
    hgreen
  · exact continuousAt_normalizedCompletedGreenState
      completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt
      completedNativeOperatorCharacteristic_zero_ne_zero hstate
  · exact hderiv

-- The provenance-preserving C3 coordinate is finite dimensional and its
-- parameter dependence is given by explicit Dirichlet-coordinate functions.
-- This local continuity fact will feed the concrete product-ledger closure.
theorem canonicalCompletedOperatorC3HilbertState_continuousAt_zero :
    ContinuousAt canonicalCompletedOperatorC3HilbertState 0 := by
  unfold canonicalCompletedOperatorC3HilbertState
  apply (WithLp.prod_continuous_toLp 2 _ _).continuousAt.comp
  have hstate : canonicalCompletedOperatorC3State =
      fun z ↦ NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
        3 (operatorHeightParameter z) := by
    funext z
    unfold canonicalCompletedOperatorC3State
    exact canonicalEnrichedC3SourcePort_eq_greenBoundaryPair
      (operatorHeightParameter z)
  rw [hstate]
  have hnatDirichlet (n : ℕ) (hn : 0 < n) :
      Continuous (fun s : ℂ ↦ natDirichletTerm s n) := by
    have hnComplex : (((n : ℤ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    unfold natDirichletTerm dirichletTerm
    exact continuous_id.neg.const_cpow (Or.inl hnComplex)
  have hpositive (n : ℕ) :
      Continuous (fun s : ℂ ↦ positiveDirichletGradient s n) := by
    unfold positiveDirichletGradient
    exact (hnatDirichlet (n + 2) (by omega)).sub
      (hnatDirichlet (n + 1) (by omega))
  have hphaseNormalizer :
      Continuous (fun s : ℂ ↦ cpPhaseNormalizer 3 s) := by
    unfold cpPhaseNormalizer
    have hexponent : Continuous
        (fun s : ℂ ↦ (1 : ℂ) / 2 + Complex.I * s.im) := by
      fun_prop
    exact hexponent.const_cpow (Or.inl (by norm_num))
  have hblock (n : ℕ) :
      Continuous (fun s : ℂ ↦ cpBlockGradient 3 s n) := by
    unfold cpBlockGradient
    apply continuous_finsetSum
    intro r hr
    exact
      (hnatDirichlet (3 * (n + 1) + r + 1) (by omega)).sub
        (hnatDirichlet (3 * (n + 1) + r) (by omega))
  have hphase (n : ℕ) : Continuous
      (fun s : ℂ ↦ phaseNormalizedCpGenuineGreenGradient 3 s n) := by
    have heq :
        (fun s : ℂ ↦ phaseNormalizedCpGenuineGreenGradient 3 s n) =
          fun s : ℂ ↦ cpPhaseNormalizer 3 s * cpBlockGradient 3 s n := by
      funext s
      rw [phaseNormalizedCpGenuineGreenGradient_eq_phaseNormalizedCpBlockGradient
        3 (by norm_num)]
      rfl
    rw [heq]
    exact hphaseNormalizer.mul (hblock n)
  have hparameter : Continuous operatorHeightParameter := by
    unfold operatorHeightParameter
    fun_prop
  apply ContinuousAt.prodMk
  · convert
      ((PiLp.continuous_toLp 2 _).comp
        (continuous_pi fun n : Fin 3 ↦
          (hphase (n : ℕ)).comp hparameter)).continuousAt using 1
    all_goals rfl
  · convert
      ((PiLp.continuous_toLp 2 _).comp
        (continuous_pi fun n : Fin 3 ↦
          (hpositive (n : ℕ)).comp hparameter)).continuousAt using 1
    all_goals rfl

/-- The concrete completed product ledger is continuous at the Taylor center
as soon as its still-abstract first factor state is continuous there.  The C3
coordinate needs no added premise: its continuity follows from its literal
finite Dirichlet coordinates. -/
theorem completedNativeC3ProductLedgerState_continuousAt_zero
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} (hxiState : ContinuousAt xiState 0) :
    ContinuousAt (completedNativeC3ProductLedgerState xiState) 0 := by
  unfold completedNativeC3ProductLedgerState weightedProductGreenState
  apply (WithLp.prod_continuous_toLp 2 _ _).continuousAt.comp
  apply ContinuousAt.prodMk
  · have hstrip : operatorHeightParameter 0 ∈ genuineCriticalStrip := by
      simpa [completedNativeHeightDomain] using
        zero_mem_completedNativeHeightDomain
    have hnativeDomain :
        operatorHeightParameter 0 ∈ nativeScalarDomain :=
      ⟨by linarith [hstrip.1], hstrip.2⟩
    exact (nativeHeightScalar_differentiableAt hnativeDomain).continuousAt.smul
      hxiState
  · have hstrip : operatorHeightParameter 0 ∈ genuineCriticalStrip := by
      simpa [completedNativeHeightDomain] using
        zero_mem_completedNativeHeightDomain
    exact (nativeXiCompletionFactor_differentiableAt hstrip).continuousAt.smul
      canonicalCompletedOperatorC3HilbertState_continuousAt_zero

/-- Concrete diagonal closure for the actual two-channel product ledger.  The
factor Green identities construct the off-diagonal relation; continuity of
the first factor state fills the collision; the finite C3 factor is already
continuous by construction. -/
theorem completedNativeC3ProductLedger_inner_self_zero_eq_responseDerivative
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) {derivative : ℂ}
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : ContinuousAt xiState 0)
    (hderiv : HasDerivAt
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) derivative 0) :
    inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) 0)
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) 0) = derivative := by
  apply
    completedNativeGreenState_inner_self_zero_eq_responseDerivative_of_continuous
      (completedNativeC3ProductLedger_greenRepresentationOn_of_factors
        xiState hxi hnative)
  · exact completedNativeC3ProductLedgerState_continuousAt_zero
      hxiContinuous
  · exact hderiv

end

end CarrySelfAdjointOperator

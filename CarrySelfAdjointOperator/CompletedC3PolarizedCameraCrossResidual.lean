import CarrySelfAdjointOperator.CompletedC3EnrichedSymplecticNoLeakBridge
import NativeCarrySpectralWeyl.Camera.DerivativeTail
import NativeCarrySpectralWeyl.Camera.QuantitativeTail

/-!
# Polarized finite-camera cross residual

The finite camera cross identity is retained first as a value channel and a
log-jet channel.  Polarization and the height rotation are applied only after
those two channels have been formed.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open Filter

noncomputable section

/-- Left value trace in the finite cross-factor identity. -/
def finiteCameraCrossLeftValue
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  factor 3 s * finiteBracketCharacteristic camera cutoff s

/-- Right value trace in the finite cross-factor identity. -/
def finiteCameraCrossRightValue
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  factor camera s * finiteBracketCharacteristic 3 cutoff s

/-- Finite cross-factor value residual between camera `camera` and the
canonical camera `3`. -/
def finiteCameraCrossValueResidual
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  finiteCameraCrossLeftValue camera cutoff s -
    finiteCameraCrossRightValue camera cutoff s

/-- Left log-jet trace, before height rotation. -/
def finiteCameraCrossLeftLogJet
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  -deriv (finiteCameraCrossLeftValue camera cutoff) s

/-- Right log-jet trace, before height rotation. -/
def finiteCameraCrossRightLogJet
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  -deriv (finiteCameraCrossRightValue camera cutoff) s

/-- The log-jet channel associated with the finite camera cross residual.
The minus sign is retained before any height-coordinate rotation. -/
def finiteCameraCrossLogJetResidual
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  -deriv (finiteCameraCrossValueResidual camera cutoff) s

/-- Infinite cross-factor residual. -/
def cameraCrossValueResidual (camera : ℕ) (s : ℂ) : ℂ :=
  factor 3 s * bracketCharacteristic camera s -
    factor camera s * bracketCharacteristic 3 s

/-- Infinite log-jet cross residual, still before height rotation. -/
def cameraCrossLogJetResidual (camera : ℕ) (s : ℂ) : ℂ :=
  -deriv (cameraCrossValueResidual camera) s

/-- Left value trace in the infinite cross-factor identity. -/
def cameraCrossLeftValue (camera : ℕ) (s : ℂ) : ℂ :=
  factor 3 s * bracketCharacteristic camera s

/-- Right value trace in the infinite cross-factor identity. -/
def cameraCrossRightValue (camera : ℕ) (s : ℂ) : ℂ :=
  factor camera s * bracketCharacteristic 3 s

/-- Left infinite log-jet trace. -/
def cameraCrossLeftLogJet (camera : ℕ) (s : ℂ) : ℂ :=
  -deriv (cameraCrossLeftValue camera) s

/-- Right infinite log-jet trace. -/
def cameraCrossRightLogJet (camera : ℕ) (s : ℂ) : ℂ :=
  -deriv (cameraCrossRightValue camera) s

/-- Polarized residual of the finite cross identity.  Each side is polarized
before subtraction. -/
def finitePolarizedCameraCrossResidual
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
      (finiteCameraCrossLeftValue camera cutoff z)
      (finiteCameraCrossLeftLogJet camera cutoff z)
      (finiteCameraCrossLeftValue camera cutoff w)
      (finiteCameraCrossLeftLogJet camera cutoff w) -
    mixedScalarBoundaryWedge
      (finiteCameraCrossRightValue camera cutoff z)
      (finiteCameraCrossRightLogJet camera cutoff z)
      (finiteCameraCrossRightValue camera cutoff w)
      (finiteCameraCrossRightLogJet camera cutoff w)

/-- Height-coordinate polarization.  The log-jet channels remain separate
until both receive the final multiplication by `i`. -/
def finiteHeightPolarizedCameraCrossResidual
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
      (finiteCameraCrossLeftValue camera cutoff z)
      (Complex.I * finiteCameraCrossLeftLogJet camera cutoff z)
      (finiteCameraCrossLeftValue camera cutoff w)
      (Complex.I * finiteCameraCrossLeftLogJet camera cutoff w) -
    mixedScalarBoundaryWedge
      (finiteCameraCrossRightValue camera cutoff z)
      (Complex.I * finiteCameraCrossRightLogJet camera cutoff z)
      (finiteCameraCrossRightValue camera cutoff w)
      (Complex.I * finiteCameraCrossRightLogJet camera cutoff w)

/-- Infinite polarized cross residual. -/
def polarizedCameraCrossResidual (camera : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
      (cameraCrossLeftValue camera z)
      (cameraCrossLeftLogJet camera z)
      (cameraCrossLeftValue camera w)
      (cameraCrossLeftLogJet camera w) -
    mixedScalarBoundaryWedge
      (cameraCrossRightValue camera z)
      (cameraCrossRightLogJet camera z)
      (cameraCrossRightValue camera w)
      (cameraCrossRightLogJet camera w)

/-- Infinite polarized cross residual after the final height rotation. -/
def heightPolarizedCameraCrossResidual
    (camera : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
      (cameraCrossLeftValue camera z)
      (Complex.I * cameraCrossLeftLogJet camera z)
      (cameraCrossLeftValue camera w)
      (Complex.I * cameraCrossLeftLogJet camera w) -
    mixedScalarBoundaryWedge
      (cameraCrossRightValue camera z)
      (Complex.I * cameraCrossRightLogJet camera z)
      (cameraCrossRightValue camera w)
      (Complex.I * cameraCrossRightLogJet camera w)

/-- Height-coordinate specialization used by the completed C3 ledger. -/
def canonicalC3FiniteHeightPolarizedCameraCrossResidual
    (camera cutoff : ℕ) (z w : ℂ) : ℂ :=
  finiteHeightPolarizedCameraCrossResidual camera cutoff
    (operatorHeightParameter z) (operatorHeightParameter w)

/-! ## First control lemmas -/

/-- The existing finite-camera estimate is exactly the norm estimate for the
new value residual. -/
theorem finiteCameraCrossValueResidual_nativeLine_norm_le
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (hcutoff : 1 ≤ cutoff)
    (t : ℝ) :
    ‖finiteCameraCrossValueResidual camera cutoff (nativeLine t)‖ ≤
      ((2 / 3 : ℝ) *
        (‖factor camera (nativeLine t)‖ * nativeTailConstant 3 t +
          ‖factor 3 (nativeLine t)‖ * nativeTailConstant camera t)) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  simpa only [finiteCameraCrossValueResidual, finiteCameraCrossLeftValue,
    finiteCameraCrossRightValue] using
    finiteBracketCharacteristic_cross_tail_le hcamera hcutoff t

/-- The value residual inherits the already formalized
`O(cutoff⁻³ᴟ²)` camera control. -/
theorem finiteCameraCrossValueResidual_nativeLine_isBigO
    {camera : ℕ} (hcamera : 2 ≤ camera) (t : ℝ) :
    (fun cutoff : ℕ =>
      finiteCameraCrossValueResidual camera cutoff (nativeLine t)) =O[atTop]
      (fun cutoff : ℕ => (cutoff : ℝ) ^ (-(3 : ℝ) / 2)) := by
  simpa only [finiteCameraCrossValueResidual, finiteCameraCrossLeftValue,
    finiteCameraCrossRightValue] using
    finiteBracketCharacteristic_cross_tail_isBigO hcamera t

/-- The value residual converges to zero on the full bracket domain.  This
uses the infinite cross-factor identity only after both finite camera limits
have been taken. -/
theorem finiteCameraCrossValueResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ =>
      finiteCameraCrossValueResidual camera cutoff s)
      atTop (nhds 0) := by
  have hcameraLimit := finiteBracketCharacteristic_tendsto hcamera hs
  have hthreeLimit := finiteBracketCharacteristic_tendsto
    (by omega : 2 ≤ 3) hs
  have hfactorThree : Tendsto (fun _ : ℕ => factor 3 s) atTop
      (nhds (factor 3 s)) := tendsto_const_nhds
  have hfactorCamera : Tendsto (fun _ : ℕ => factor camera s) atTop
      (nhds (factor camera s)) := tendsto_const_nhds
  have hlimit :=
    (hfactorThree.mul hcameraLimit).sub
      (hfactorCamera.mul hthreeLimit)
  have hcross := bracketCharacteristic_cross_eq hcamera hs
  simpa only [finiteCameraCrossValueResidual, finiteCameraCrossLeftValue,
    finiteCameraCrossRightValue, hcross, sub_self] using hlimit

/-- The infinite value residual is exactly zero throughout the bracket
domain. -/
theorem cameraCrossValueResidual_eq_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossValueResidual camera s = 0 := by
  unfold cameraCrossValueResidual
  exact sub_eq_zero.mpr (bracketCharacteristic_cross_eq hcamera hs)

/-- The infinite log-jet residual is also zero.  The proof differentiates
the cross identity on a neighborhood rather than discarding factor
derivatives pointwise. -/
theorem cameraCrossLogJetResidual_eq_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLogJetResidual camera s = 0 := by
  have heq : cameraCrossValueResidual camera =ᶠ[nhds s]
      (fun _ : ℂ => 0) := by
    filter_upwards [isOpen_bracketDomain.mem_nhds hs] with u hu
    exact cameraCrossValueResidual_eq_zero hcamera hu
  unfold cameraCrossLogJetResidual
  rw [heq.deriv_eq]
  simp

/-- Pointwise convergence of the finite characteristic derivatives, obtained
from the existing locally uniform convergence theorem. -/
theorem deriv_finiteBracketCharacteristic_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto
      (fun cutoff : ℕ =>
        deriv (finiteBracketCharacteristic camera cutoff) s)
      atTop (nhds (deriv (bracketCharacteristic camera) s)) := by
  have hderivConvergence :=
    (finiteBracketCharacteristic_tendstoLocallyUniformlyOn hcamera).deriv
      (Filter.Eventually.of_forall fun cutoff =>
        (finiteBracketCharacteristic_differentiable hcamera cutoff).differentiableOn)
      isOpen_bracketDomain
  simpa only [Function.comp_apply] using hderivConvergence.tendsto_at hs

/-- Product-rule expansion of the cross residual before the minus derivative
is renamed as the log-jet channel. -/
theorem hasDerivAt_finiteCameraCrossValueResidual
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    HasDerivAt (finiteCameraCrossValueResidual camera cutoff)
      (deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
          factor 3 s *
            finiteBracketCharacteristicExponentDeriv camera cutoff s -
        (deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
          factor camera s *
            finiteBracketCharacteristicExponentDeriv 3 cutoff s)) s := by
  unfold finiteCameraCrossValueResidual
  exact
    (((factor_differentiable (by omega : 2 ≤ 3)).differentiableAt.hasDerivAt.mul
        (finiteBracketCharacteristic_hasDerivAt hcamera cutoff s)).sub
      ((factor_differentiable hcamera).differentiableAt.hasDerivAt.mul
        (finiteBracketCharacteristic_hasDerivAt (by omega : 2 ≤ 3) cutoff s)))

/-- Explicit separated formula for the log-jet residual.  In particular the
derivatives of the camera factors are retained. -/
theorem finiteCameraCrossLogJetResidual_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossLogJetResidual camera cutoff s =
      -(deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
          factor 3 s *
            finiteBracketCharacteristicExponentDeriv camera cutoff s -
        (deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
          factor camera s *
            finiteBracketCharacteristicExponentDeriv 3 cutoff s)) := by
  unfold finiteCameraCrossLogJetResidual
  rw [(hasDerivAt_finiteCameraCrossValueResidual hcamera cutoff s).deriv]

/-- The same finite log-jet expansion, stated using ordinary derivatives of
the two finite characteristics. -/
theorem finiteCameraCrossLogJetResidual_eq_deriv
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossLogJetResidual camera cutoff s =
      -(deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
          factor 3 s * deriv (finiteBracketCharacteristic camera cutoff) s -
        (deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
          factor camera s *
            deriv (finiteBracketCharacteristic 3 cutoff) s)) := by
  rw [finiteCameraCrossLogJetResidual_eq hcamera]
  rw [deriv_finiteBracketCharacteristic hcamera,
    deriv_finiteBracketCharacteristic (by omega : 2 ≤ 3)]

/-- Product-rule expansion of the infinite cross residual. -/
theorem hasDerivAt_cameraCrossValueResidual
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    HasDerivAt (cameraCrossValueResidual camera)
      (deriv (factor 3) s * bracketCharacteristic camera s +
          factor 3 s * deriv (bracketCharacteristic camera) s -
        (deriv (factor camera) s * bracketCharacteristic 3 s +
          factor camera s * deriv (bracketCharacteristic 3) s)) s := by
  have hcameraCharacteristic :
      DifferentiableAt ℂ (bracketCharacteristic camera) s :=
    (bracketCharacteristic_differentiableOn hcamera).differentiableAt
      (isOpen_bracketDomain.mem_nhds hs)
  have hthreeCharacteristic :
      DifferentiableAt ℂ (bracketCharacteristic 3) s :=
    (bracketCharacteristic_differentiableOn (by omega : 2 ≤ 3)).differentiableAt
      (isOpen_bracketDomain.mem_nhds hs)
  unfold cameraCrossValueResidual
  exact
    (((factor_differentiable (by omega : 2 ≤ 3)).differentiableAt.hasDerivAt.mul
        hcameraCharacteristic.hasDerivAt).sub
      ((factor_differentiable hcamera).differentiableAt.hasDerivAt.mul
        hthreeCharacteristic.hasDerivAt))

/-- Infinite log-jet expansion with all factor derivatives retained. -/
theorem cameraCrossLogJetResidual_eq_deriv
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLogJetResidual camera s =
      -(deriv (factor 3) s * bracketCharacteristic camera s +
          factor 3 s * deriv (bracketCharacteristic camera) s -
        (deriv (factor camera) s * bracketCharacteristic 3 s +
          factor camera s * deriv (bracketCharacteristic 3) s)) := by
  unfold cameraCrossLogJetResidual
  rw [(hasDerivAt_cameraCrossValueResidual hcamera hs).deriv]

/-- The finite log-jet cross residual converges to zero on the bracket domain.
This is the derivative-level counterpart of the value-channel limit. -/
theorem finiteCameraCrossLogJetResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ =>
      finiteCameraCrossLogJetResidual camera cutoff s)
      atTop (nhds 0) := by
  have hcameraValue := finiteBracketCharacteristic_tendsto hcamera hs
  have hthreeValue := finiteBracketCharacteristic_tendsto
    (by omega : 2 ≤ 3) hs
  have hcameraDeriv :=
    deriv_finiteBracketCharacteristic_tendsto hcamera hs
  have hthreeDeriv :=
    deriv_finiteBracketCharacteristic_tendsto (by omega : 2 ≤ 3) hs
  have hfactorThree : Tendsto (fun _ : ℕ => factor 3 s) atTop
      (nhds (factor 3 s)) := tendsto_const_nhds
  have hfactorCamera : Tendsto (fun _ : ℕ => factor camera s) atTop
      (nhds (factor camera s)) := tendsto_const_nhds
  have hfactorThreeDeriv : Tendsto (fun _ : ℕ => deriv (factor 3) s) atTop
      (nhds (deriv (factor 3) s)) := tendsto_const_nhds
  have hfactorCameraDeriv :
      Tendsto (fun _ : ℕ => deriv (factor camera) s) atTop
        (nhds (deriv (factor camera) s)) := tendsto_const_nhds
  have hleft :=
    (hfactorThreeDeriv.mul hcameraValue).add
      (hfactorThree.mul hcameraDeriv)
  have hright :=
    (hfactorCameraDeriv.mul hthreeValue).add
      (hfactorCamera.mul hthreeDeriv)
  have hformula := (hleft.sub hright).neg
  have hlimit : Tendsto (fun cutoff : ℕ =>
      finiteCameraCrossLogJetResidual camera cutoff s)
      atTop (nhds (cameraCrossLogJetResidual camera s)) := by
    simpa only [finiteCameraCrossLogJetResidual_eq_deriv hcamera,
      cameraCrossLogJetResidual_eq_deriv hcamera hs] using hformula
  simpa only [cameraCrossLogJetResidual_eq_zero hcamera hs] using hlimit

/-! ## Convergence of the two polarized sides -/

theorem hasDerivAt_finiteCameraCrossLeftValue
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    HasDerivAt (finiteCameraCrossLeftValue camera cutoff)
      (deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
        factor 3 s *
          deriv (finiteBracketCharacteristic camera cutoff) s) s := by
  unfold finiteCameraCrossLeftValue
  exact
    (factor_differentiable (by omega : 2 ≤ 3)).differentiableAt.hasDerivAt.mul
      (finiteBracketCharacteristic_differentiable hcamera cutoff).differentiableAt.hasDerivAt

theorem hasDerivAt_finiteCameraCrossRightValue
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    HasDerivAt (finiteCameraCrossRightValue camera cutoff)
      (deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
        factor camera s * deriv (finiteBracketCharacteristic 3 cutoff) s) s := by
  unfold finiteCameraCrossRightValue
  exact
    (factor_differentiable hcamera).differentiableAt.hasDerivAt.mul
      (finiteBracketCharacteristic_differentiable
        (by omega : 2 ≤ 3) cutoff).differentiableAt.hasDerivAt

theorem finiteCameraCrossLeftLogJet_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossLeftLogJet camera cutoff s =
      -(deriv (factor 3) s * finiteBracketCharacteristic camera cutoff s +
        factor 3 s * deriv (finiteBracketCharacteristic camera cutoff) s) := by
  unfold finiteCameraCrossLeftLogJet
  rw [(hasDerivAt_finiteCameraCrossLeftValue hcamera cutoff s).deriv]

theorem finiteCameraCrossRightLogJet_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossRightLogJet camera cutoff s =
      -(deriv (factor camera) s * finiteBracketCharacteristic 3 cutoff s +
        factor camera s * deriv (finiteBracketCharacteristic 3 cutoff) s) := by
  unfold finiteCameraCrossRightLogJet
  rw [(hasDerivAt_finiteCameraCrossRightValue hcamera cutoff s).deriv]

theorem hasDerivAt_cameraCrossLeftValue
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    HasDerivAt (cameraCrossLeftValue camera)
      (deriv (factor 3) s * bracketCharacteristic camera s +
        factor 3 s * deriv (bracketCharacteristic camera) s) s := by
  have hcharacteristic : DifferentiableAt ℂ (bracketCharacteristic camera) s :=
    (bracketCharacteristic_differentiableOn hcamera).differentiableAt
      (isOpen_bracketDomain.mem_nhds hs)
  unfold cameraCrossLeftValue
  exact
    (factor_differentiable (by omega : 2 ≤ 3)).differentiableAt.hasDerivAt.mul
      hcharacteristic.hasDerivAt

theorem hasDerivAt_cameraCrossRightValue
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    HasDerivAt (cameraCrossRightValue camera)
      (deriv (factor camera) s * bracketCharacteristic 3 s +
        factor camera s * deriv (bracketCharacteristic 3) s) s := by
  have hcharacteristic : DifferentiableAt ℂ (bracketCharacteristic 3) s :=
    (bracketCharacteristic_differentiableOn (by omega : 2 ≤ 3)).differentiableAt
      (isOpen_bracketDomain.mem_nhds hs)
  unfold cameraCrossRightValue
  exact
    (factor_differentiable hcamera).differentiableAt.hasDerivAt.mul
      hcharacteristic.hasDerivAt

theorem cameraCrossLeftLogJet_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLeftLogJet camera s =
      -(deriv (factor 3) s * bracketCharacteristic camera s +
        factor 3 s * deriv (bracketCharacteristic camera) s) := by
  unfold cameraCrossLeftLogJet
  rw [(hasDerivAt_cameraCrossLeftValue hcamera hs).deriv]

theorem cameraCrossRightLogJet_eq
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossRightLogJet camera s =
      -(deriv (factor camera) s * bracketCharacteristic 3 s +
        factor camera s * deriv (bracketCharacteristic 3) s) := by
  unfold cameraCrossRightLogJet
  rw [(hasDerivAt_cameraCrossRightValue hcamera hs).deriv]

theorem finiteCameraCrossLeftValue_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ => finiteCameraCrossLeftValue camera cutoff s)
      atTop (nhds (cameraCrossLeftValue camera s)) := by
  have hfactor : Tendsto (fun _ : ℕ => factor 3 s) atTop
      (nhds (factor 3 s)) := tendsto_const_nhds
  simpa only [finiteCameraCrossLeftValue, cameraCrossLeftValue] using
    hfactor.mul (finiteBracketCharacteristic_tendsto hcamera hs)

theorem finiteCameraCrossRightValue_tendsto
    {camera : ℕ} (_hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ => finiteCameraCrossRightValue camera cutoff s)
      atTop (nhds (cameraCrossRightValue camera s)) := by
  have hfactor : Tendsto (fun _ : ℕ => factor camera s) atTop
      (nhds (factor camera s)) := tendsto_const_nhds
  simpa only [finiteCameraCrossRightValue, cameraCrossRightValue] using
    hfactor.mul (finiteBracketCharacteristic_tendsto
      (by omega : 2 ≤ 3) hs)

theorem finiteCameraCrossLeftLogJet_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ => finiteCameraCrossLeftLogJet camera cutoff s)
      atTop (nhds (cameraCrossLeftLogJet camera s)) := by
  have hvalue := finiteBracketCharacteristic_tendsto hcamera hs
  have hderiv := deriv_finiteBracketCharacteristic_tendsto hcamera hs
  have hfactor : Tendsto (fun _ : ℕ => factor 3 s) atTop
      (nhds (factor 3 s)) := tendsto_const_nhds
  have hfactorDeriv : Tendsto (fun _ : ℕ => deriv (factor 3) s) atTop
      (nhds (deriv (factor 3) s)) := tendsto_const_nhds
  have hformula := ((hfactorDeriv.mul hvalue).add (hfactor.mul hderiv)).neg
  simpa only [finiteCameraCrossLeftLogJet_eq hcamera,
    cameraCrossLeftLogJet_eq hcamera hs] using hformula

theorem finiteCameraCrossRightLogJet_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ => finiteCameraCrossRightLogJet camera cutoff s)
      atTop (nhds (cameraCrossRightLogJet camera s)) := by
  have hvalue := finiteBracketCharacteristic_tendsto
    (by omega : 2 ≤ 3) hs
  have hderiv := deriv_finiteBracketCharacteristic_tendsto
    (by omega : 2 ≤ 3) hs
  have hfactor : Tendsto (fun _ : ℕ => factor camera s) atTop
      (nhds (factor camera s)) := tendsto_const_nhds
  have hfactorDeriv :
      Tendsto (fun _ : ℕ => deriv (factor camera) s) atTop
        (nhds (deriv (factor camera) s)) := tendsto_const_nhds
  have hformula := ((hfactorDeriv.mul hvalue).add (hfactor.mul hderiv)).neg
  simpa only [finiteCameraCrossRightLogJet_eq hcamera,
    cameraCrossRightLogJet_eq hcamera hs] using hformula

theorem cameraCrossLeftValue_eq_rightValue
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLeftValue camera s = cameraCrossRightValue camera s := by
  unfold cameraCrossLeftValue cameraCrossRightValue
  exact bracketCharacteristic_cross_eq hcamera hs

theorem cameraCrossLeftLogJet_eq_rightLogJet
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    cameraCrossLeftLogJet camera s = cameraCrossRightLogJet camera s := by
  have heq : cameraCrossLeftValue camera =ᶠ[nhds s]
      cameraCrossRightValue camera := by
    filter_upwards [isOpen_bracketDomain.mem_nhds hs] with u hu
    exact cameraCrossLeftValue_eq_rightValue hcamera hu
  unfold cameraCrossLeftLogJet cameraCrossRightLogJet
  rw [heq.deriv_eq]

/-- The finite log-jet residual is exactly the difference of the two retained
log-jet sides. -/
theorem finiteCameraCrossLogJetResidual_eq_left_sub_right
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    finiteCameraCrossLogJetResidual camera cutoff s =
      finiteCameraCrossLeftLogJet camera cutoff s -
        finiteCameraCrossRightLogJet camera cutoff s := by
  unfold finiteCameraCrossLogJetResidual finiteCameraCrossValueResidual
    finiteCameraCrossLeftLogJet finiteCameraCrossRightLogJet
  have hleft := hasDerivAt_finiteCameraCrossLeftValue hcamera cutoff s
  have hright := hasDerivAt_finiteCameraCrossRightValue hcamera cutoff s
  have hsub := hleft.sub hright
  change -deriv
      (finiteCameraCrossLeftValue camera cutoff -
        finiteCameraCrossRightValue camera cutoff) s = _
  rw [hsub.deriv, hleft.deriv, hright.deriv]
  ring

/-- Four-term expansion of the polarized residual.  Every term contains an
explicit value or log-jet cross residual, so no cancellation is hidden inside
the final wedge subtraction. -/
theorem finitePolarizedCameraCrossResidual_eq_residualExpansion
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (z w : ℂ) :
    finitePolarizedCameraCrossResidual camera cutoff z w =
      finiteCameraCrossLogJetResidual camera cutoff z *
          (starRingEnd ℂ) (finiteCameraCrossLeftValue camera cutoff w) +
        finiteCameraCrossRightLogJet camera cutoff z *
          (starRingEnd ℂ) (finiteCameraCrossValueResidual camera cutoff w) -
        finiteCameraCrossValueResidual camera cutoff z *
          (starRingEnd ℂ) (finiteCameraCrossLeftLogJet camera cutoff w) -
        finiteCameraCrossRightValue camera cutoff z *
          (starRingEnd ℂ) (finiteCameraCrossLogJetResidual camera cutoff w) := by
  rw [finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff z,
    finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff w]
  unfold finitePolarizedCameraCrossResidual finiteCameraCrossValueResidual
    mixedScalarBoundaryWedge
  simp only [map_sub]
  ring

/-- Height-rotated version of the four-term residual expansion.  Rotation is
still applied only at this final polarized readout. -/
theorem finiteHeightPolarizedCameraCrossResidual_eq_residualExpansion
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (z w : ℂ) :
    finiteHeightPolarizedCameraCrossResidual camera cutoff z w =
      (Complex.I * finiteCameraCrossLogJetResidual camera cutoff z) *
          (starRingEnd ℂ) (finiteCameraCrossLeftValue camera cutoff w) +
        (Complex.I * finiteCameraCrossRightLogJet camera cutoff z) *
          (starRingEnd ℂ) (finiteCameraCrossValueResidual camera cutoff w) -
        finiteCameraCrossValueResidual camera cutoff z *
          (starRingEnd ℂ)
            (Complex.I * finiteCameraCrossLeftLogJet camera cutoff w) -
        finiteCameraCrossRightValue camera cutoff z *
          (starRingEnd ℂ)
            (Complex.I * finiteCameraCrossLogJetResidual camera cutoff w) := by
  rw [finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff z,
    finiteCameraCrossLogJetResidual_eq_left_sub_right hcamera cutoff w]
  unfold finiteHeightPolarizedCameraCrossResidual
    finiteCameraCrossValueResidual mixedScalarBoundaryWedge
  simp only [mul_sub, map_sub]
  ring

theorem polarizedCameraCrossResidual_eq_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    polarizedCameraCrossResidual camera z w = 0 := by
  unfold polarizedCameraCrossResidual
  rw [cameraCrossLeftValue_eq_rightValue hcamera hz,
    cameraCrossLeftLogJet_eq_rightLogJet hcamera hz,
    cameraCrossLeftValue_eq_rightValue hcamera hw,
    cameraCrossLeftLogJet_eq_rightLogJet hcamera hw]
  ring

theorem heightPolarizedCameraCrossResidual_eq_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    heightPolarizedCameraCrossResidual camera z w = 0 := by
  unfold heightPolarizedCameraCrossResidual
  rw [cameraCrossLeftValue_eq_rightValue hcamera hz,
    cameraCrossLeftLogJet_eq_rightLogJet hcamera hz,
    cameraCrossLeftValue_eq_rightValue hcamera hw,
    cameraCrossLeftLogJet_eq_rightLogJet hcamera hw]
  ring

theorem finitePolarizedCameraCrossResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ =>
      finitePolarizedCameraCrossResidual camera cutoff z w)
      atTop (nhds 0) := by
  have hzLeftValue := finiteCameraCrossLeftValue_tendsto hcamera hz
  have hzLeftLogJet := finiteCameraCrossLeftLogJet_tendsto hcamera hz
  have hwLeftValue := finiteCameraCrossLeftValue_tendsto hcamera hw
  have hwLeftLogJet := finiteCameraCrossLeftLogJet_tendsto hcamera hw
  have hzRightValue := finiteCameraCrossRightValue_tendsto hcamera hz
  have hzRightLogJet := finiteCameraCrossRightLogJet_tendsto hcamera hz
  have hwRightValue := finiteCameraCrossRightValue_tendsto hcamera hw
  have hwRightLogJet := finiteCameraCrossRightLogJet_tendsto hcamera hw
  have hleft :=
    (hzLeftLogJet.mul hwLeftValue.star).sub
      (hzLeftValue.mul hwLeftLogJet.star)
  have hright :=
    (hzRightLogJet.mul hwRightValue.star).sub
      (hzRightValue.mul hwRightLogJet.star)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      finitePolarizedCameraCrossResidual camera cutoff z w)
      atTop (nhds (polarizedCameraCrossResidual camera z w)) := by
    simpa [finitePolarizedCameraCrossResidual,
      polarizedCameraCrossResidual, mixedScalarBoundaryWedge] using
        hleft.sub hright
  simpa only [polarizedCameraCrossResidual_eq_zero hcamera hz hw] using hlimit

theorem finiteHeightPolarizedCameraCrossResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : z ∈ bracketDomain) (hw : w ∈ bracketDomain) :
    Tendsto (fun cutoff : ℕ =>
      finiteHeightPolarizedCameraCrossResidual camera cutoff z w)
      atTop (nhds 0) := by
  have hzLeftValue := finiteCameraCrossLeftValue_tendsto hcamera hz
  have hzLeftLogJet :=
    (finiteCameraCrossLeftLogJet_tendsto hcamera hz).const_mul Complex.I
  have hwLeftValue := finiteCameraCrossLeftValue_tendsto hcamera hw
  have hwLeftLogJet :=
    (finiteCameraCrossLeftLogJet_tendsto hcamera hw).const_mul Complex.I
  have hzRightValue := finiteCameraCrossRightValue_tendsto hcamera hz
  have hzRightLogJet :=
    (finiteCameraCrossRightLogJet_tendsto hcamera hz).const_mul Complex.I
  have hwRightValue := finiteCameraCrossRightValue_tendsto hcamera hw
  have hwRightLogJet :=
    (finiteCameraCrossRightLogJet_tendsto hcamera hw).const_mul Complex.I
  have hleft :=
    (hzLeftLogJet.mul hwLeftValue.star).sub
      (hzLeftValue.mul hwLeftLogJet.star)
  have hright :=
    (hzRightLogJet.mul hwRightValue.star).sub
      (hzRightValue.mul hwRightLogJet.star)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      finiteHeightPolarizedCameraCrossResidual camera cutoff z w)
      atTop (nhds (heightPolarizedCameraCrossResidual camera z w)) := by
    simpa [finiteHeightPolarizedCameraCrossResidual,
      heightPolarizedCameraCrossResidual, mixedScalarBoundaryWedge] using
        hleft.sub hright
  simpa only [heightPolarizedCameraCrossResidual_eq_zero hcamera hz hw] using hlimit

/-- The canonical height-coordinate residual tends to zero throughout the
product critical strip. -/
theorem canonicalC3FiniteHeightPolarizedCameraCrossResidual_tendsto_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto (fun cutoff : ℕ =>
      canonicalC3FiniteHeightPolarizedCameraCrossResidual
        camera cutoff z w) atTop (nhds 0) := by
  have hzDomain : operatorHeightParameter z ∈ bracketDomain := by
    change -1 < (operatorHeightParameter z).re
    linarith [hz.1]
  have hwDomain : operatorHeightParameter w ∈ bracketDomain := by
    change -1 < (operatorHeightParameter w).re
    linarith [hw.1]
  simpa only [canonicalC3FiniteHeightPolarizedCameraCrossResidual] using
    finiteHeightPolarizedCameraCrossResidual_tendsto_zero
      hcamera hzDomain hwDomain


end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedC3PolarizedCameraCrossResidual

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

namespace CanonicalC3BracketTfvdCompletionState

/-- Chart-normalized value read from an arbitrary completed bracket--TFVD
state.  The state still retains its head, tail, and Green port separately. -/
def normalizedValueAt {M : ℕ}
    (state : CanonicalC3BracketTfvdCompletionState M) (z : ℂ) : ℂ :=
  state.valueReadout /
    cpChartFactor 3 (operatorHeightParameter z)

/-- Height-rotated normalized log-jet read from the same state. -/
def normalizedLogJetAt {M : ℕ}
    (state : CanonicalC3BracketTfvdCompletionState M) (z : ℂ) : ℂ :=
  let s := operatorHeightParameter z
  Complex.I *
    ((state.logJetReadout * cpChartFactor 3 s +
        state.valueReadout * deriv (cpChartFactor 3) s) /
      cpChartFactor 3 s ^ 2)

/-- Xi-completed value projection of an arbitrary completed bracket--TFVD
state. -/
def completedValueAt {M : ℕ}
    (state : CanonicalC3BracketTfvdCompletionState M) (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z * state.normalizedValueAt z

/-- Xi product companion, formed only after the value and log-jet channels
have been read separately. -/
def boundaryCompanionAt {M : ℕ}
    (state : CanonicalC3BracketTfvdCompletionState M) (z : ℂ) : ℂ :=
  nativeXiCompletionBoundaryCompanion z * state.normalizedValueAt z +
    nativeXiCompletionFactor z * state.normalizedLogJetAt z

/-- The two completed scalar traces of one structured TFVD state. -/
def completedTraceAt {M : ℕ}
    (state : CanonicalC3BracketTfvdCompletionState M) (z : ℂ) : ℂ × ℂ :=
  (state.completedValueAt z, state.boundaryCompanionAt z)

/-- On the canonical state, the generic state-level trace projection is
definitionally the existing completed bracket--TFVD trace pair. -/
theorem completedTraceAt_canonical (M : ℕ) (z : ℂ) :
    (canonicalC3BracketTfvdCompletionState M
      (operatorHeightParameter z)).completedTraceAt z =
      canonicalC3BracketTfvdCompletedTracePair M z := by
  rfl

end CanonicalC3BracketTfvdCompletionState

/-- Four logical completed traces with every head and tail still stored as
separate Hilbert coordinates.  The outer pair corresponds to `z` and `w`. -/
abbrev CanonicalC3SeparatedFourTraceHilbert :=
  WithLp 2
    (CanonicalCompletedC3AllCutoffOnePointTraceHilbert ×
      CanonicalCompletedC3AllCutoffOnePointTraceHilbert)

/-- Three fixed six-camera Naimark vectors retained before either real
symplectic skew is evaluated. -/
abbrev CanonicalC3SixCameraSymplecticGreenCarrierHilbert :=
  WithLp 2
    (RealifiedNaimarkComplexification ×
      WithLp 2
        (RealifiedNaimarkComplexification ×
          RealifiedNaimarkComplexification))

namespace CanonicalC3SixCameraSymplecticGreenCarrierHilbert

def direct (state : CanonicalC3SixCameraSymplecticGreenCarrierHilbert) :
    RealifiedNaimarkComplexification :=
  state.fst

def reflected (state : CanonicalC3SixCameraSymplecticGreenCarrierHilbert) :
    RealifiedNaimarkComplexification :=
  state.snd.fst

def quarterTurnReflected
    (state : CanonicalC3SixCameraSymplecticGreenCarrierHilbert) :
    RealifiedNaimarkComplexification :=
  state.snd.snd

/-- The two real skew channels are read only after all three Naimark vectors
have been retained. -/
def quadratures (state : CanonicalC3SixCameraSymplecticGreenCarrierHilbert) :
    FiniteC3SymplecticGreenQuadratures where
  direct := realifiedGreenSkew state.direct state.reflected
  quarterTurn := realifiedGreenSkew state.direct state.quarterTurnReflected

/-- Pythagorean audit of the three independent Naimark coordinates. -/
theorem norm_sq_eq_vector_sum
    (state : CanonicalC3SixCameraSymplecticGreenCarrierHilbert) :
    ‖state‖ ^ 2 =
      ‖state.direct‖ ^ 2 +
        ‖state.reflected‖ ^ 2 + ‖state.quarterTurnReflected‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2 state,
    WithLp.prod_norm_sq_eq_of_L2 state.snd]
  unfold direct reflected quarterTurnReflected
  ring

end CanonicalC3SixCameraSymplecticGreenCarrierHilbert

/-- The canonical complete C3 block required by the four scalar traces and
the reflected Green pair.  The reflected state is explicit because it is not
the scalar `z` state. -/
structure CanonicalC3FourTraceSixCameraSource where
  zState : CanonicalC3BracketTfvdCompletionState 1
  wState : CanonicalC3BracketTfvdCompletionState 1
  reflectedZState : CanonicalC3BracketTfvdCompletionState 1

namespace CanonicalC3FourTraceSixCameraSource

/-- Head/tail vector of one source state, before completion or
normalization. -/
def separatedTrace {M : ℕ}
    (state : CanonicalC3BracketTfvdCompletionState M) :
    CanonicalCompletedC3AllCutoffOnePointTraceHilbert :=
  WithLp.toLp 2
    (state.transport.valueReadout,
      WithLp.toLp 2
        (state.transport.logJetReadout,
          WithLp.toLp 2 (state.valueTail, state.logJetTail)))

/-- Both `z` and `w` head/tail vectors.  No Wronskian or scalar sum is taken
here. -/
def separatedFourTraceProjection
    (source : CanonicalC3FourTraceSixCameraSource) :
    CanonicalC3SeparatedFourTraceHilbert :=
  WithLp.toLp 2
    (separatedTrace source.zState, separatedTrace source.wState)

/-- Four completed scalar traces, still arranged as the two trace pairs at
`z` and `w`. -/
def completedFourTraceProjection
    (z w : ℂ) (source : CanonicalC3FourTraceSixCameraSource) :
    (ℂ × ℂ) × (ℂ × ℂ) :=
  (source.zState.completedTraceAt z,
    source.wState.completedTraceAt w)

/-- Direct and reflected complete C3 ports from the same mixed source. -/
def greenPortProjection
    (source : CanonicalC3FourTraceSixCameraSource) :
    FiniteC3GreenPortCarrier 3 × FiniteC3GreenPortCarrier 3 :=
  (source.wState.greenPort, source.reflectedZState.greenPort)

/-- Full vector Green projection through the fixed realization supported on
cameras `2, ..., 7`, before either skew pairing. -/
def sixCameraGreenCarrierProjection
    (source : CanonicalC3FourTraceSixCameraSource) :
    CanonicalC3SixCameraSymplecticGreenCarrierHilbert :=
  WithLp.toLp 2
    (canonicalC3SymplecticNaimarkRealization source.greenPortProjection.1,
      WithLp.toLp 2
        (canonicalC3SymplecticNaimarkRealization source.greenPortProjection.2,
          canonicalC3SymplecticNaimarkRealization
            (Complex.I • source.greenPortProjection.2)))

/-- The two real symplectic quadratures of the projected Green ports. -/
def sixCameraGreenQuadratures
    (source : CanonicalC3FourTraceSixCameraSource) :
    FiniteC3SymplecticGreenQuadratures :=
  source.sixCameraGreenCarrierProjection.quadratures

/-- The final complex readout is delayed until both real quadratures have
been retained. -/
def sixCameraGreenComplexReadout
    (source : CanonicalC3FourTraceSixCameraSource) : ℂ :=
  source.sixCameraGreenQuadratures.complexReadout

end CanonicalC3FourTraceSixCameraSource

/-- Canonical mixed source at two operator-height parameters. -/
def canonicalC3FourTraceSixCameraSource
    (z w : ℂ) : CanonicalC3FourTraceSixCameraSource where
  zState := canonicalC3BracketTfvdCompletionState 1
    (operatorHeightParameter z)
  wState := canonicalC3BracketTfvdCompletionState 1
    (operatorHeightParameter w)
  reflectedZState := canonicalC3BracketTfvdCompletionState 1
    (reflectedParameter (operatorHeightParameter z))

/-- Canonical head/tail state of the four logical traces at the complete C3
block. -/
def canonicalC3SeparatedFourTraceState
    (z w : ℂ) : CanonicalC3SeparatedFourTraceHilbert :=
  WithLp.toLp 2
    (WithLp.toLp 2
      (finiteBracketedDirichletChart 3 1 (operatorHeightParameter z),
        WithLp.toLp 2
          (finiteCanonicalLogBracketChart 1 (operatorHeightParameter z),
            WithLp.toLp 2
              (realCpBracketCutoffTail 3 1 (operatorHeightParameter z),
                canonicalC3LogJetCutoffTail 1 (operatorHeightParameter z)))),
      WithLp.toLp 2
        (finiteBracketedDirichletChart 3 1 (operatorHeightParameter w),
          WithLp.toLp 2
            (finiteCanonicalLogBracketChart 1 (operatorHeightParameter w),
              WithLp.toLp 2
                (realCpBracketCutoffTail 3 1 (operatorHeightParameter w),
                  canonicalC3LogJetCutoffTail 1
                    (operatorHeightParameter w)))))

/-- Canonical three-vector carrier using exactly the fixed six-camera C3
realization. -/
def canonicalC3MixedSixCameraSymplecticCarrier
    (z w : ℂ) : CanonicalC3SixCameraSymplecticGreenCarrierHilbert :=
  let direct := finiteC3GenuineBracketGreenBoundaryPair 3 w
  let reflected := finiteC3GenuineBracketGreenBoundaryPair
    3 (reflectedParameter z)
  WithLp.toLp 2
    (canonicalC3SymplecticNaimarkRealization direct,
      WithLp.toLp 2
        (canonicalC3SymplecticNaimarkRealization reflected,
          canonicalC3SymplecticNaimarkRealization
            (Complex.I • reflected)))

/-- Head, log-jet, and both exact tails at `z` and `w` are recovered
coordinatewise from the canonical mixed source. -/
theorem canonicalC3FourTraceSixCameraSource_separatedTrace_eq
    (z w : ℂ) :
    (canonicalC3FourTraceSixCameraSource z w).separatedFourTraceProjection =
      canonicalC3SeparatedFourTraceState z w := by
  unfold CanonicalC3FourTraceSixCameraSource.separatedFourTraceProjection
    CanonicalC3FourTraceSixCameraSource.separatedTrace
    canonicalC3FourTraceSixCameraSource canonicalC3SeparatedFourTraceState
  rw [(canonicalC3BracketTfvdCompletionState_transport_components
      1 (operatorHeightParameter z)).1,
    (canonicalC3BracketTfvdCompletionState_transport_components
      1 (operatorHeightParameter z)).2.1,
    (canonicalC3BracketTfvdCompletionState_transport_components
      1 (operatorHeightParameter w)).1,
    (canonicalC3BracketTfvdCompletionState_transport_components
      1 (operatorHeightParameter w)).2.1]
  rfl

/-- The four completed trace coordinates of the same source are exactly
`(F(z), -F'(z), F(w), -F'(w))`. -/
theorem canonicalC3FourTraceSixCameraSource_completedFourTrace_eq_F_negFprime
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalC3FourTraceSixCameraSource z w).completedFourTraceProjection z w =
      ((completedNativeOperatorCharacteristic z,
          -deriv completedNativeOperatorCharacteristic z),
        (completedNativeOperatorCharacteristic w,
          -deriv completedNativeOperatorCharacteristic w)) := by
  unfold CanonicalC3FourTraceSixCameraSource.completedFourTraceProjection
    canonicalC3FourTraceSixCameraSource
  rw [CanonicalC3BracketTfvdCompletionState.completedTraceAt_canonical,
    CanonicalC3BracketTfvdCompletionState.completedTraceAt_canonical,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime 1 hz,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime 1 hw]

/-- The two Green coordinates of that source are exactly the direct bracket
port at `w` and the reflected bracket port at `z`. -/
theorem canonicalC3FourTraceSixCameraSource_greenPort_eq_bracket
    (z w : ℂ) :
    (canonicalC3FourTraceSixCameraSource z w).greenPortProjection =
      (finiteC3GenuineBracketGreenBoundaryPair 3 (operatorHeightParameter w),
        finiteC3GenuineBracketGreenBoundaryPair
          3 (reflectedParameter (operatorHeightParameter z))) := by
  unfold CanonicalC3FourTraceSixCameraSource.greenPortProjection
    canonicalC3FourTraceSixCameraSource
  rw [canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket,
    canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket]

/-- The Green side of the mixed source is an equality of all three fixed
six-camera Naimark vectors, before any skew or scalar reconstruction. -/
theorem canonicalC3FourTraceSixCameraSource_symplecticCarrier_eq
    (z w : ℂ) :
    (canonicalC3FourTraceSixCameraSource z w).sixCameraGreenCarrierProjection =
      canonicalC3MixedSixCameraSymplecticCarrier
        (operatorHeightParameter z) (operatorHeightParameter w) := by
  unfold CanonicalC3FourTraceSixCameraSource.sixCameraGreenCarrierProjection
    canonicalC3MixedSixCameraSymplecticCarrier
  rw [canonicalC3FourTraceSixCameraSource_greenPort_eq_bracket]

/-- Complete vector bridge: separated heads/tails and all three fixed
six-camera Naimark vectors are projections of one mixed source. -/
theorem canonicalC3FourTraceSixCameraVectorBridge
    (z w : ℂ) :
    ((canonicalC3FourTraceSixCameraSource z w).separatedFourTraceProjection =
        canonicalC3SeparatedFourTraceState z w) ∧
      ((canonicalC3FourTraceSixCameraSource z w).sixCameraGreenCarrierProjection =
        canonicalC3MixedSixCameraSymplecticCarrier
          (operatorHeightParameter z) (operatorHeightParameter w)) := by
  exact ⟨canonicalC3FourTraceSixCameraSource_separatedTrace_eq z w,
    canonicalC3FourTraceSixCameraSource_symplecticCarrier_eq z w⟩

/-- Completed capstone of the vector bridge.  The four scalar traces and the
three fixed six-camera Naimark vectors are identified coordinatewise; neither
side is contracted to a Wronskian or Green scalar in this theorem. -/
theorem canonicalC3FourTraceSixCameraCompletedVectorBridge
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    ((canonicalC3FourTraceSixCameraSource z w).completedFourTraceProjection
        z w =
      ((completedNativeOperatorCharacteristic z,
          -deriv completedNativeOperatorCharacteristic z),
        (completedNativeOperatorCharacteristic w,
          -deriv completedNativeOperatorCharacteristic w))) ∧
      ((canonicalC3FourTraceSixCameraSource z w).sixCameraGreenCarrierProjection =
        canonicalC3MixedSixCameraSymplecticCarrier
          (operatorHeightParameter z) (operatorHeightParameter w)) := by
  exact
    ⟨canonicalC3FourTraceSixCameraSource_completedFourTrace_eq_F_negFprime
        hz hw,
      canonicalC3FourTraceSixCameraSource_symplecticCarrier_eq z w⟩

/-- The two real quadratures read from the vector carrier are exactly the
quadratures underlying the existing fixed six-camera complex readout. -/
theorem canonicalC3FourTraceSixCameraSource_complexReadout_eq_existing
    (z w : ℂ) :
    (canonicalC3FourTraceSixCameraSource z w).sixCameraGreenComplexReadout =
      canonicalC3SixCameraSymplecticComplexReadout
        (finiteC3GenuineBracketGreenBoundaryPair 3
          (operatorHeightParameter w))
        (finiteC3GenuineBracketGreenBoundaryPair 3
          (reflectedParameter (operatorHeightParameter z))) := by
  unfold CanonicalC3FourTraceSixCameraSource.sixCameraGreenComplexReadout
    CanonicalC3FourTraceSixCameraSource.sixCameraGreenQuadratures
    CanonicalC3SixCameraSymplecticGreenCarrierHilbert.quadratures
    CanonicalC3SixCameraSymplecticGreenCarrierHilbert.direct
    CanonicalC3SixCameraSymplecticGreenCarrierHilbert.reflected
    CanonicalC3SixCameraSymplecticGreenCarrierHilbert.quarterTurnReflected
    CanonicalC3FourTraceSixCameraSource.sixCameraGreenCarrierProjection
    canonicalC3SixCameraSymplecticComplexReadout
  rw [canonicalC3FourTraceSixCameraSource_greenPort_eq_bracket]
  rfl

/-- Applying the final fixed six-camera readout to the vector Green
projection reconstructs the complete complex Green form. -/
theorem canonicalC3FourTraceSixCameraSource_greenReadout_eq_greenForm
    (z w : ℂ) :
    (canonicalC3FourTraceSixCameraSource z w).sixCameraGreenComplexReadout =
      greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair 3
          (operatorHeightParameter w))
        (finiteC3GenuineBracketGreenBoundaryPair 3
          (reflectedParameter (operatorHeightParameter z))) := by
  rw [canonicalC3FourTraceSixCameraSource_complexReadout_eq_existing,
    canonicalC3SixCameraSymplecticComplexReadout_eq_greenForm]

end

end CarrySelfAdjointOperator

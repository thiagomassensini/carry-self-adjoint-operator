import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedDependency
import CarrySelfAdjointOperator.CompletedC3EnrichedSymplecticNoLeakBridge
import CarrySelfAdjointOperator.C3TwoVariableGreenGamma
import CarrySelfAdjointOperator.BR2RadialNormalizedComplexJetNoGo

/-!
# Undressed Green carriers for the independent-reflected C3 presentation

The completed source reconstruction has a natural Green carrier before the
real radial multiplier used by `greenPort`.  This file keeps that carrier
separate, records the exact two-leg dressing map, and lifts the separation to
the camera-resolved pairwise Green expression.

The separation is deliberately algebraic.  It does not make a complex
analytic claim for the reconstructed reflected source; the corresponding
conditional interface is stated below in terms of analyticity of its ordinary
component.
-/

open scoped BigOperators lp ENNReal NNReal ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open CanonicalC3AllCutoffMixedSourceHilbert

noncomputable section
set_option autoImplicit false

/-- The Green carrier prior to the radial normalization.  Both Green legs
read the ordinary reconstructed source; no real-coordinate multiplier is
present here. -/
def undressedGreenPort
    (N : ℕ) (state : CanonicalCompletedC3HilbertState) :
    FiniteC3GreenPortCarrier N :=
  (WithLp.toLp 2 (fun n : Fin N => state.1 (n : ℕ)),
    WithLp.toLp 2 (fun n : Fin N => state.1 (n : ℕ)))

@[simp] theorem undressedGreenPort_fst_apply
    (N : ℕ) (state : CanonicalCompletedC3HilbertState) (n : Fin N) :
    (undressedGreenPort N state).1 n = state.1 (n : ℕ) :=
  rfl

@[simp] theorem undressedGreenPort_snd_apply
    (N : ℕ) (state : CanonicalCompletedC3HilbertState) (n : Fin N) :
    (undressedGreenPort N state).2 n = state.1 (n : ℕ) :=
  rfl

/-- The exact Green-carrier action of a scalar radial multiplier.  It acts on
the first leg only, matching the public `greenPort` extractor. -/
def radialGreenDress {N : ℕ} (rho : ℂ)
    (port : FiniteC3GreenPortCarrier N) : FiniteC3GreenPortCarrier N :=
  (rho • port.1, port.2)

@[simp] theorem radialGreenDress_fst_apply
    {N : ℕ} (rho : ℂ) (port : FiniteC3GreenPortCarrier N) (n : Fin N) :
    (radialGreenDress rho port).1 n = rho * port.1 n := by
  rfl

@[simp] theorem radialGreenDress_snd_apply
    {N : ℕ} (rho : ℂ) (port : FiniteC3GreenPortCarrier N) (n : Fin N) :
    (radialGreenDress rho port).2 n = port.2 n :=
  rfl

@[simp] theorem radialGreenDress_one
    {N : ℕ} (port : FiniteC3GreenPortCarrier N) :
    radialGreenDress 1 port = port := by
  apply Prod.ext <;> ext n <;> simp [radialGreenDress]

/-- The real radial factor appearing in the first coordinate of `greenPort`.
Giving it a name permits its action to be stated without changing that public
definition. -/
def c3RadialGreenFactor (s : ℂ) : ℂ :=
  (((3 : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ)

/-- Coordinate form of the first, radially dressed leg of `greenPort`. -/
theorem greenPort_fst_apply
    (N : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState) (n : Fin N) :
    (greenPort N s state).1 n = c3RadialGreenFactor s * state.1 (n : ℕ) :=
  rfl

/-- Coordinate form of the second, undressed leg of `greenPort`. -/
theorem greenPort_snd_apply
    (N : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState) (n : Fin N) :
    (greenPort N s state).2 n = state.1 (n : ℕ) :=
  rfl

/-- `greenPort` is exactly the radial dressing of its prior carrier. -/
theorem greenPort_eq_radialGreenDress_undressedGreenPort
    (N : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState) :
    greenPort N s state =
      radialGreenDress (c3RadialGreenFactor s) (undressedGreenPort N state) := by
  apply Prod.ext <;> ext n <;>
    simp [greenPort, radialGreenDress, c3RadialGreenFactor, undressedGreenPort]

/-- Along the independent reflected coordinate, the radial factor used by the
normalized Green presentation. -/
def canonicalC3IndependentReflectedRadialGreenFactor (v : ℂ) : ℂ :=
  c3RadialGreenFactor (operatorHeightParameter v)

@[simp] theorem canonicalC3IndependentReflectedRadialGreenFactor_zero :
    canonicalC3IndependentReflectedRadialGreenFactor 0 = 1 := by
  norm_num [canonicalC3IndependentReflectedRadialGreenFactor,
    c3RadialGreenFactor, operatorHeightParameter, criticalDisplacement]

/-- The radial factor used here is exactly the BR2 final-readout phase.  This
identifies the shared external dressing without assigning complex jets to it. -/
theorem canonicalC3IndependentReflectedRadialGreenFactor_eq_br2RadialPhase
    (v : ℂ) :
    canonicalC3IndependentReflectedRadialGreenFactor v = br2RadialPhase v := by
  unfold canonicalC3IndependentReflectedRadialGreenFactor c3RadialGreenFactor
    br2RadialPhase
  change (((3 : ℝ) ^
      (-criticalDisplacement (operatorHeightParameter v).re) : ℝ) : ℂ) =
    (Real.exp (br2RadialExponent v) : ℂ)
  norm_cast
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  simp [br2RadialExponent, operatorHeightParameter, criticalDisplacement,
    Complex.mul_re]

/-! ## Comparison with the established raw C3 port -/

/-- The diagonal positive-gradient carrier which arises from an undressed
ordinary prefix. -/
def finiteC3PositiveDiagonalGreenBoundaryPair (M : ℕ) (s : ℂ) :
    FiniteC3GreenBoundarySpace M × FiniteC3GreenBoundarySpace M :=
  (WithLp.toLp 2 (fun n : Fin M => positiveDirichletGradient s n),
    WithLp.toLp 2 (fun n : Fin M => positiveDirichletGradient s n))

@[simp] theorem finiteC3PositiveDiagonalGreenBoundaryPair_fst_apply
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteC3PositiveDiagonalGreenBoundaryPair M s).1 n =
      positiveDirichletGradient s n :=
  rfl

@[simp] theorem finiteC3PositiveDiagonalGreenBoundaryPair_snd_apply
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteC3PositiveDiagonalGreenBoundaryPair M s).2 n =
      positiveDirichletGradient s n :=
  rfl

/-- The historical raw C3 Green port is not the diagonal carrier: it is its
holomorphic eigenvalue dressing on the first leg. -/
theorem finiteC3HolomorphicGenuineGreenBoundaryPair_eq_eigenvalueDress
    (M : ℕ) (s : ℂ) :
    finiteC3HolomorphicGenuineGreenBoundaryPair M s =
      radialGreenDress (natDirichletTerm s 3)
        (finiteC3PositiveDiagonalGreenBoundaryPair M s) := by
  apply Prod.ext
  · ext n
    rw [finiteC3HolomorphicGenuineGreenBoundaryPair_fst_apply,
      cpGenuineGreenGradient_eq_cpBlockGradient 3 (by norm_num),
      cpBlockGradient_eq_eigenvalue_mul]
    rfl
  · ext n
    rfl

/-- On the finite canonical ordinary prefix, the new undressed extractor is
literally the diagonal positive-gradient carrier. -/
theorem undressedGreenPort_prefix_eq_positiveDiagonal
    (M : ℕ) (s : ℂ) :
    undressedGreenPort M (canonicalCompletedC3HilbertPrefixState s M) =
      finiteC3PositiveDiagonalGreenBoundaryPair M s := by
  apply Prod.ext <;> ext n
  · simp [undressedGreenPort, canonicalCompletedC3HilbertPrefixState,
      canonicalCompletedC3DirichletGradientPrefixState_apply]
  · change canonicalCompletedC3DirichletGradientPrefixState s M (n : ℕ) =
      positiveDirichletGradient s n
    simp [canonicalCompletedC3DirichletGradientPrefixState_apply, n.isLt]

/-! ## Independent-reflected source ports -/

/-- The direct camera port before radial normalization. -/
def cameraResolvedIndependentReflectedUndressedDirectGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  undressedGreenPort (3 * M)
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v camera).wSource

/-- The reflected camera port before radial normalization.  Its definition
contains no radial factor; it is the ordinary reconstructed reflected source
in both Green legs. -/
def cameraResolvedIndependentReflectedUndressedReflectedGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  undressedGreenPort (3 * M)
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v camera).reflectedZSource

/-- The normalized direct port is its undressed port: its source parameter is
the centered height, where the radial factor is one. -/
theorem cameraResolvedIndependentReflectedDirectGreenPort_eq_undressed
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedDirectGreenPort M q hq0 hq1 S u v camera =
      cameraResolvedIndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u v camera := by
  rw [show cameraResolvedIndependentReflectedDirectGreenPort M q hq0 hq1 S u v camera =
      greenPort (3 * M) (operatorHeightParameter 0)
        (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
          M q hq0 hq1 S u v camera).wSource by rfl,
    greenPort_eq_radialGreenDress_undressedGreenPort]
  simp [cameraResolvedIndependentReflectedUndressedDirectGreenPort,
    c3RadialGreenFactor, operatorHeightParameter, criticalDisplacement]

/-- The normalized reflected port is exactly the radial dressing of the
undressed reflected port. -/
theorem cameraResolvedIndependentReflectedReflectedGreenPort_eq_radialGreenDress_undressed
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedReflectedGreenPort M q hq0 hq1 S u v camera =
      radialGreenDress (canonicalC3IndependentReflectedRadialGreenFactor v)
        (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
          M q hq0 hq1 S u v camera) := by
  exact greenPort_eq_radialGreenDress_undressedGreenPort (3 * M)
    (operatorHeightParameter v)
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v camera).reflectedZSource

/-- The camera-resolved normalization is the BR2 radial phase applied only
after the undressed Green carrier has been formed. -/
theorem cameraResolvedIndependentReflectedReflectedGreenPort_eq_br2FinalDress_undressed
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedReflectedGreenPort M q hq0 hq1 S u v camera =
      radialGreenDress (br2RadialPhase v)
        (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
          M q hq0 hq1 S u v camera) := by
  rw [← canonicalC3IndependentReflectedRadialGreenFactor_eq_br2RadialPhase]
  exact cameraResolvedIndependentReflectedReflectedGreenPort_eq_radialGreenDress_undressed
    M q hq0 hq1 S u v camera

/-! ## The exact Green-form crosswalk -/

/-- The pairwise Green expression before radial dressing. -/
def canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ)
    (directCamera reflectedCamera : ℕ) : ℂ :=
  greenForm
    (cameraResolvedIndependentReflectedUndressedDirectGreenPort
      M q hq0 hq1 S u v directCamera)
    (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
      M q hq0 hq1 S u v reflectedCamera)

/-- Applying a first-leg dressing inside `greenForm` produces an exact
radial-difference term.  It is not assumed to vanish. -/
theorem greenForm_radialGreenDress_right
    {N : ℕ} (rho : ℂ) (direct reflected : FiniteC3GreenPortCarrier N) :
    greenForm direct (radialGreenDress rho reflected) =
      greenForm direct reflected +
        (rho - 1) * inner ℂ direct.2 reflected.1 := by
  unfold radialGreenDress greenForm
  rw [inner_smul_right]
  ring

/-- The existing normalized pairwise kernel equals the undressed kernel plus
the precise radial-difference contribution. -/
theorem canonicalC3CameraResolvedIndependentReflectedGreenKernel_eq_undressed_add_radial
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedGreenKernel
      M q hq0 hq1 S u v directCamera reflectedCamera =
      canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
        M q hq0 hq1 S u v directCamera reflectedCamera +
        (canonicalC3IndependentReflectedRadialGreenFactor v - 1) *
          inner ℂ
            (cameraResolvedIndependentReflectedUndressedDirectGreenPort
              M q hq0 hq1 S u v directCamera).2
            (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
              M q hq0 hq1 S u v reflectedCamera).1 := by
  unfold canonicalC3CameraResolvedIndependentReflectedGreenKernel
    canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
  rw [cameraResolvedIndependentReflectedDirectGreenPort_eq_undressed,
    cameraResolvedIndependentReflectedReflectedGreenPort_eq_radialGreenDress_undressed,
    greenForm_radialGreenDress_right]

/-! ## Fixed-atlas undressed carrier -/

/-- Undressed extraction preserves addition of reconstructed states. -/
theorem undressedGreenPort_add
    (N : ℕ) (state₁ state₂ : CanonicalCompletedC3HilbertState) :
    undressedGreenPort N (state₁ + state₂) =
      undressedGreenPort N state₁ + undressedGreenPort N state₂ := by
  apply Prod.ext <;> ext n <;> simp [undressedGreenPort]

/-- A finite sum commutes with the undressed extraction from the direct
source projection. -/
theorem undressedGreenPort_wSource_finset_sum
    (N : ℕ) {ι : Type*} (A : Finset ι)
    (f : ι → CanonicalC3AllCutoffMixedSourceHilbert) :
    undressedGreenPort N (∑ i ∈ A, f i).wSource =
      ∑ i ∈ A, undressedGreenPort N (f i).wSource := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      apply Prod.ext <;> ext n <;>
        simp [undressedGreenPort, CanonicalC3AllCutoffMixedSourceHilbert.wSource]
  | insert a A ha ih =>
      rw [Finset.sum_insert ha,
        canonicalC3AllCutoffMixedSourceHilbert_wSource_add,
        undressedGreenPort_add, ih, Finset.sum_insert ha]

/-- A finite sum commutes with the undressed extraction from the reflected
source projection. -/
theorem undressedGreenPort_reflectedZSource_finset_sum
    (N : ℕ) {ι : Type*} (A : Finset ι)
    (f : ι → CanonicalC3AllCutoffMixedSourceHilbert) :
    undressedGreenPort N (∑ i ∈ A, f i).reflectedZSource =
      ∑ i ∈ A, undressedGreenPort N (f i).reflectedZSource := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      apply Prod.ext <;> ext n <;>
        simp [undressedGreenPort,
          CanonicalC3AllCutoffMixedSourceHilbert.reflectedZSource]
  | insert a A ha ih =>
      rw [Finset.sum_insert ha,
        canonicalC3AllCutoffMixedSourceHilbert_reflectedZSource_add,
        undressedGreenPort_add, ih, Finset.sum_insert ha]

/-- The canonical direct port before radial normalization. -/
def canonicalC3IndependentReflectedUndressedDirectGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  undressedGreenPort (3 * M)
    (canonicalC3IndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v).wSource

/-- The canonical reflected port before radial normalization. -/
def canonicalC3IndependentReflectedUndressedReflectedGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  undressedGreenPort (3 * M)
    (canonicalC3IndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v).reflectedZSource

/-- The normalized canonical reflected port is the radial dressing of the
canonical undressed port. -/
theorem canonicalC3IndependentReflectedReflectedGreenPort_eq_radialGreenDress_undressed
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedReflectedGreenPort M q hq0 hq1 S u v =
      radialGreenDress (canonicalC3IndependentReflectedRadialGreenFactor v)
        (canonicalC3IndependentReflectedUndressedReflectedGreenPort
          M q hq0 hq1 S u v) := by
  exact greenPort_eq_radialGreenDress_undressedGreenPort (3 * M)
    (operatorHeightParameter v)
    (canonicalC3IndependentReflectedSixSourceReconstruction M q hq0 hq1 S u v).reflectedZSource

/-- The normalized canonical direct port agrees with its undressed port. -/
theorem canonicalC3IndependentReflectedDirectGreenPort_eq_undressed
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedDirectGreenPort M q hq0 hq1 S u v =
      canonicalC3IndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u v := by
  rw [show canonicalC3IndependentReflectedDirectGreenPort M q hq0 hq1 S u v =
      greenPort (3 * M) (operatorHeightParameter 0)
        (canonicalC3IndependentReflectedSixSourceReconstruction M q hq0 hq1 S u v).wSource by
      rfl,
    greenPort_eq_radialGreenDress_undressedGreenPort]
  simp [canonicalC3IndependentReflectedUndressedDirectGreenPort,
    c3RadialGreenFactor, operatorHeightParameter, criticalDisplacement]

/-- The fixed finite camera sum of undressed direct ports is the canonical
undressed direct port. -/
theorem cameraResolvedIndependentReflectedUndressedDirectGreenPort_sum_eq_canonical
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedIndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u v camera =
      canonicalC3IndependentReflectedUndressedDirectGreenPort M q hq0 hq1 S u v := by
  unfold cameraResolvedIndependentReflectedUndressedDirectGreenPort
    canonicalC3IndependentReflectedUndressedDirectGreenPort
  rw [← undressedGreenPort_wSource_finset_sum,
    cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_sum_eq_canonical]

/-- The fixed finite camera sum of undressed reflected ports is the canonical
undressed reflected port. -/
theorem cameraResolvedIndependentReflectedUndressedReflectedGreenPort_sum_eq_canonical
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedIndependentReflectedUndressedReflectedGreenPort
        M q hq0 hq1 S u v camera =
      canonicalC3IndependentReflectedUndressedReflectedGreenPort M q hq0 hq1 S u v := by
  unfold cameraResolvedIndependentReflectedUndressedReflectedGreenPort
    canonicalC3IndependentReflectedUndressedReflectedGreenPort
  rw [← undressedGreenPort_reflectedZSource_finset_sum,
    cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_sum_eq_canonical]

/-- The canonical Green expression before radial normalization. -/
def canonicalC3IndependentReflectedUndressedGreenBoundary
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) : ℂ :=
  greenForm
    (canonicalC3IndependentReflectedUndressedDirectGreenPort M q hq0 hq1 S u v)
    (canonicalC3IndependentReflectedUndressedReflectedGreenPort M q hq0 hq1 S u v)

/-- The undressed canonical Green carrier is the fixed finite sum of its
pairwise undressed camera kernels. -/
theorem canonicalC3IndependentReflectedUndressedGreenBoundary_eq_cameraPairwise
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedUndressedGreenBoundary M q hq0 hq1 S u v =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
            M q hq0 hq1 S u v directCamera reflectedCamera := by
  unfold canonicalC3IndependentReflectedUndressedGreenBoundary
    canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
  rw [← cameraResolvedIndependentReflectedUndressedDirectGreenPort_sum_eq_canonical,
    ← cameraResolvedIndependentReflectedUndressedReflectedGreenPort_sum_eq_canonical]
  exact greenForm_finset_sum_pairwise
    (canonicalFiniteCameraAtlas M) (canonicalFiniteCameraAtlas M)
    (cameraResolvedIndependentReflectedUndressedDirectGreenPort M q hq0 hq1 S u v)
    (cameraResolvedIndependentReflectedUndressedReflectedGreenPort M q hq0 hq1 S u v)

/-- The normalized canonical Green boundary has the same exact
undressed-plus-radial-difference crosswalk as every camera pair. -/
theorem canonicalC3IndependentReflectedCorrectedGreenBoundary_eq_undressed_add_radial
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedCorrectedGreenBoundary M q hq0 hq1 S u v =
      canonicalC3IndependentReflectedUndressedGreenBoundary M q hq0 hq1 S u v +
        (canonicalC3IndependentReflectedRadialGreenFactor v - 1) *
          inner ℂ
            (canonicalC3IndependentReflectedUndressedDirectGreenPort
              M q hq0 hq1 S u v).2
            (canonicalC3IndependentReflectedUndressedReflectedGreenPort
              M q hq0 hq1 S u v).1 := by
  unfold canonicalC3IndependentReflectedCorrectedGreenBoundary
    canonicalC3IndependentReflectedUndressedGreenBoundary
  rw [canonicalC3IndependentReflectedDirectGreenPort_eq_undressed,
    canonicalC3IndependentReflectedReflectedGreenPort_eq_radialGreenDress_undressed,
    greenForm_radialGreenDress_right]

/-! ## Analytic interface of the undressed extraction -/

/-- The finite ordinary-coordinate readout as a continuous linear map. -/
def undressedGreenPortLeg (N : ℕ) :
    CarryVerticalL2 →L[ℂ] FiniteC3GreenBoundarySpace N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun n : Fin N =>
      lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 (n : ℕ)))

/-- The continuous linear map from an ordinary source to the two-leg
undressed Green carrier. -/
def undressedGreenPortFromOrdinary (N : ℕ) :
    CarryVerticalL2 →L[ℂ] FiniteC3GreenPortCarrier N :=
  let leg := undressedGreenPortLeg N
  leg.prod leg

/-- The pointwise definition of `undressedGreenPort` is exactly the
continuous linear ordinary-coordinate extractor. -/
theorem undressedGreenPort_eq_fromOrdinary
    (N : ℕ) (state : CanonicalCompletedC3HilbertState) :
    undressedGreenPort N state =
      undressedGreenPortFromOrdinary N state.1 := by
  apply Prod.ext <;> ext n <;>
    simp [undressedGreenPort, undressedGreenPortFromOrdinary,
      undressedGreenPortLeg, lp.evalCLM]

/-- A continuous linear undressed extraction preserves analyticity of an
ordinary source. -/
theorem undressedGreenPortFromOrdinary_analyticAt_zero
    (N : ℕ) (source : ℂ → CarryVerticalL2)
    (hsource : AnalyticAt ℂ source 0) :
    AnalyticAt ℂ (fun v => undressedGreenPortFromOrdinary N (source v)) 0 := by
  simpa only [Function.comp_def] using
    ((undressedGreenPortFromOrdinary N).analyticAt (source 0)).comp hsource

/-- Any analytic ordinary source remains analytic after undressed Green-port
extraction.  This theorem has no radial hypothesis. -/
theorem undressedGreenPort_analyticAt_zero_of_ordinary
    (N : ℕ) (source : ℂ → CanonicalCompletedC3HilbertState)
    (hsource : AnalyticAt ℂ (fun v => (source v).1) 0) :
    AnalyticAt ℂ (fun v => undressedGreenPort N (source v)) 0 := by
  rw [show (fun v => undressedGreenPort N (source v)) =
      fun v => undressedGreenPortFromOrdinary N (source v).1 by
        funext v
        exact undressedGreenPort_eq_fromOrdinary N (source v)]
  exact undressedGreenPortFromOrdinary_analyticAt_zero N
    (fun v => (source v).1) hsource

/-- The undressed direct port inherits the already established independence
of its reconstructed source. -/
theorem cameraResolvedIndependentReflectedUndressedDirectGreenPort_independent
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ v₁ u₂ v₂ : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedUndressedDirectGreenPort
      M q hq0 hq1 S u₁ v₁ camera =
    cameraResolvedIndependentReflectedUndressedDirectGreenPort
      M q hq0 hq1 S u₂ v₂ camera := by
  unfold cameraResolvedIndependentReflectedUndressedDirectGreenPort
  rw [cameraResolvedIndependentReflectedSixSourceReconstruction_wSource_independent]

/-- The undressed reflected port is independent of the direct coordinate. -/
theorem cameraResolvedIndependentReflectedUndressedReflectedGreenPort_independent_u
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ u₂ v : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedUndressedReflectedGreenPort
      M q hq0 hq1 S u₁ v camera =
    cameraResolvedIndependentReflectedUndressedReflectedGreenPort
      M q hq0 hq1 S u₂ v camera := by
  unfold cameraResolvedIndependentReflectedUndressedReflectedGreenPort
  rw [cameraResolvedIndependentReflectedSixSourceReconstruction_reflectedZSource_independent_u]

/-- The direct undressed port is analytic in the independent reflected
coordinate because it is constant there. -/
theorem cameraResolvedIndependentReflectedUndressedDirectGreenPort_analyticAt_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (camera : ℕ) :
    AnalyticAt ℂ
      (fun v => cameraResolvedIndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u v camera) 0 := by
  have hfun :
      (fun v => cameraResolvedIndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u v camera) =
      fun _ : ℂ => cameraResolvedIndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u 0 camera := by
    funext v
    exact cameraResolvedIndependentReflectedUndressedDirectGreenPort_independent
      M q hq0 hq1 S u v u 0 camera
  rw [hfun]
  exact analyticAt_const

/-- Conditional analytic interface for the reflected undressed port.  The
remaining hypothesis is precisely analyticity of the reconstructed ordinary
reflected source, before any Green-port dressing is applied. -/
theorem cameraResolvedIndependentReflectedUndressedReflectedGreenPort_analyticAt_zero_of_reconstructedOrdinary
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (camera : ℕ)
    (hsource : AnalyticAt ℂ
      (fun v =>
        (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
          M q hq0 hq1 S u v camera).reflectedZSource.1) 0) :
    AnalyticAt ℂ
      (fun v => cameraResolvedIndependentReflectedUndressedReflectedGreenPort
        M q hq0 hq1 S u v camera) 0 := by
  exact undressedGreenPort_analyticAt_zero_of_ordinary (3 * M)
    (fun v =>
      (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
        M q hq0 hq1 S u v camera).reflectedZSource) hsource

/-! ## Final physical section -/

/-- On the physical section, the established reflected port is obtained by
first forming the undressed independent carrier and then applying its radial
dressing. -/
theorem cameraResolvedReflectedGreenPort_physicalSection_eq_radialGreenDress_undressed
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (camera : ℕ) :
    cameraResolvedReflectedGreenPort M (operatorHeightParameter u)
      (operatorHeightParameter 0) q hq0 hq1 S camera =
      radialGreenDress
        (canonicalC3IndependentReflectedRadialGreenFactor ((starRingEnd ℂ) u))
        (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
          M q hq0 hq1 S u ((starRingEnd ℂ) u) camera) := by
  rw [← cameraResolvedIndependentReflectedReflectedGreenPort_physicalSection]
  exact cameraResolvedIndependentReflectedReflectedGreenPort_eq_radialGreenDress_undressed
    M q hq0 hq1 S u ((starRingEnd ℂ) u) camera

/-- The physical pairwise kernel is the physical section of the exact
undressed-plus-radial-difference formula. -/
theorem canonicalC3CameraResolvedCorrectedGreenKernel_physicalSection_eq_undressed_add_radial
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedCorrectedGreenKernel M
      (operatorHeightParameter u) (operatorHeightParameter 0)
      q hq0 hq1 S directCamera reflectedCamera =
      canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
        M q hq0 hq1 S u ((starRingEnd ℂ) u) directCamera reflectedCamera +
        (canonicalC3IndependentReflectedRadialGreenFactor ((starRingEnd ℂ) u) - 1) *
          inner ℂ
            (cameraResolvedIndependentReflectedUndressedDirectGreenPort
              M q hq0 hq1 S u ((starRingEnd ℂ) u) directCamera).2
            (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
              M q hq0 hq1 S u ((starRingEnd ℂ) u) reflectedCamera).1 := by
  rw [← canonicalC3CameraResolvedIndependentReflectedGreenKernel_physicalSection]
  exact canonicalC3CameraResolvedIndependentReflectedGreenKernel_eq_undressed_add_radial
    M q hq0 hq1 S u ((starRingEnd ℂ) u) directCamera reflectedCamera

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeCameraUniversality
import Mathlib.Tactic

/-!
# Local Hadamard jets from the completed native characteristic

The coefficients here come from the completed native characteristic, not
from a prescribed zero list or Hadamard product. A simple real zero is
needed only to interpret the deflated coefficients as the Taylor
coefficients of F(gamma+v)/(v*F'(gamma)).

The local logarithmic moments are defined by a division-free (up to the
nonzero constant term) coefficient recurrence. Their independence of
camera/cutoff is inherited from the exact completed-camera identity.
No RH, all-order positivity, or spectral-zero assumption is used.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators
noncomputable section

/-- Coefficient of order n after shifting an analytic characteristic to
gamma and removing one zero factor, normalized by its first derivative.
At a simple zero gamma this is the coefficient of
F(gamma+v)/(v*F'(gamma)). -/
def nativeLocalDeflatedCoefficient (gamma : ℝ) (n : ℕ) : ℂ :=
  (iteratedDeriv (n + 1) completedNativeOperatorCharacteristic (gamma : ℂ) /
      ((n + 1).factorial : ℂ)) /
    iteratedDeriv 1 completedNativeOperatorCharacteristic (gamma : ℂ)

/-- The identical local coefficient read from one completed and
camera-normalized head-plus-exact-tail presentation. -/
def cameraLocalDeflatedCoefficient
    (camera cutoff : ℕ) (gamma : ℝ) (n : ℕ) : ℂ :=
  (iteratedDeriv (n + 1)
        (normalizedCompletedNativeCameraCharacteristic camera cutoff) gamma /
      ((n + 1).factorial : ℂ)) /
    iteratedDeriv 1
      (normalizedCompletedNativeCameraCharacteristic camera cutoff) gamma

/-- All deflated Taylor coefficients are independent of the camera and
of the geometric cutoff, without any zero-location hypothesis. -/
theorem cameraLocalDeflatedCoefficient_eq_native
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff : ℕ) (gamma : ℝ) (n : ℕ) :
    cameraLocalDeflatedCoefficient camera cutoff gamma n =
      nativeLocalDeflatedCoefficient gamma n := by
  unfold cameraLocalDeflatedCoefficient nativeLocalDeflatedCoefficient
  rw [iteratedDeriv_normalizedCompletedNativeCameraCharacteristic
      hcamera cutoff (n + 1) gamma,
    iteratedDeriv_normalizedCompletedNativeCameraCharacteristic
      hcamera cutoff 1 gamma]

/-- Exact algebra of pole removal from Phi(u)=(u-a)*B(u).
The expression before adding 1/(u-a) is -Phi'/Phi. -/
theorem localLogDerivative_pole_removal
    (u a b db : ℂ) (hu : u ≠ a) (hb : b ≠ 0) :
    -(b + (u - a) * db) / ((u - a) * b) + 1 / (u - a) =
      -db / b := by
  have hdiff : u - a ≠ 0 := sub_ne_zero.mpr hu
  field_simp
  ring

/-- Analytic version of local pole removal: if Phi(u)=(u-a)*B(u)
and B is differentiable and nonzero at u, the regularized logarithmic
derivative is exactly -B'(u)/B(u). No product over zeros is involved. -/
theorem localLogDerivative_pole_removal_of_factor
    (Phi B : ℂ → ℂ) (a u : ℂ)
    (hfac : Phi = fun z => (z - a) * B z)
    (hB : DifferentiableAt ℂ B u)
    (hu : u ≠ a) (hb : B u ≠ 0) :
    -deriv Phi u / Phi u + 1 / (u - a) =
      -deriv B u / B u := by
  have hlinear : HasDerivAt (fun z : ℂ => z - a) 1 u :=
    (hasDerivAt_id u).sub_const a
  have hmul := hlinear.mul hB.hasDerivAt
  have hderiv : deriv Phi u = B u + (u - a) * deriv B u := by
    rw [hfac]
    change deriv ((fun z : ℂ => z - a) * B) u = _
    simpa only [one_mul] using hmul.deriv
  rw [hderiv, hfac]
  exact localLogDerivative_pole_removal u a (B u) (deriv B u) hu hb

/-- The quadratic height change u=(gamma+v)^2 produces exactly the
reflected-zero term 1/(2*gamma+v) after the anchor pole is removed.
The variable q is the global negative logarithmic derivative -Phi'/Phi. -/
theorem localHeightResponse_pole_removal
    (gamma v q : ℂ) (hv : v ≠ 0)
    (hmirror : 2 * gamma + v ≠ 0) :
    -2 * (gamma + v) * q - 1 / v =
      1 / (2 * gamma + v) -
        2 * (gamma + v) *
          (q + 1 / ((gamma + v)^2 - gamma^2)) := by
  have hquad :
      (gamma + v)^2 - gamma^2 = v * (2 * gamma + v) := by ring
  rw [hquad]
  field_simp
  ring

/-- Purely coefficient-theoretic logarithmic derivative of a power
series a(v) with a(0) nonzero. It solves c(v)*a(v)=a'(v).
Unlike a root-sum formula this definition is valid for any coefficient
sequence; division by a(0) is explicit. -/
def localLogDerivativeCoefficients (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (((n + 1 : ℕ) : ℂ) * a (n + 1) -
    ∑ k ∈ (Finset.range n).attach,
      localLogDerivativeCoefficients a (k : ℕ) * a (n - (k : ℕ))) / a 0
termination_by n
decreasing_by
  exact Finset.mem_range.mp k.property

/-- A simple root gives constant term one in the normalized
deflated jet, as required for the local logarithmic expansion. -/
theorem nativeLocalDeflatedCoefficient_zero
    (gamma : ℝ)
    (hsimple :
      iteratedDeriv 1 completedNativeOperatorCharacteristic (gamma : ℂ) ≠ 0) :
    nativeLocalDeflatedCoefficient gamma 0 = 1 := by
  have hd : deriv completedNativeOperatorCharacteristic (gamma : ℂ) ≠ 0 := by
    simpa only [iteratedDeriv_one] using hsimple
  simp [nativeLocalDeflatedCoefficient, hd]

/-- Coefficient recurrence, including the constant term. -/
theorem localLogDerivativeCoefficients_recurrence
    (a : ℕ → ℂ) (ha : a 0 ≠ 0) (n : ℕ) :
    localLogDerivativeCoefficients a n * a 0 +
      ∑ k ∈ (Finset.range n).attach,
        localLogDerivativeCoefficients a (k : ℕ) * a (n - (k : ℕ)) =
      ((n + 1 : ℕ) : ℂ) * a (n + 1) := by
  rw [localLogDerivativeCoefficients]
  rw [div_mul_cancel₀ _ ha]
  ring

/-- Historical local S_m convention: S_m=(-1)^(m-1) times
the coefficient of v^(m-1) in G'(v)/G(v). -/
def localHadamardMoment (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else
    (-1 : ℂ)^(m - 1) * localLogDerivativeCoefficients a (m - 1)

def nativeLocalHadamardMoment (gamma : ℝ) (m : ℕ) : ℂ :=
  localHadamardMoment (nativeLocalDeflatedCoefficient gamma) m

def cameraLocalHadamardMoment
    (camera cutoff : ℕ) (gamma : ℝ) (m : ℕ) : ℂ :=
  localHadamardMoment (cameraLocalDeflatedCoefficient camera cutoff gamma) m

/-- All local Hadamard moments (including S6 and S7) are
camera/cutoff-independent. -/
theorem cameraLocalHadamardMoment_eq_native
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff : ℕ) (gamma : ℝ) (m : ℕ) :
    cameraLocalHadamardMoment camera cutoff gamma m =
      nativeLocalHadamardMoment gamma m := by
  unfold cameraLocalHadamardMoment nativeLocalHadamardMoment
  congr 1
  funext n
  exact cameraLocalDeflatedCoefficient_eq_native
    hcamera cutoff gamma n

theorem nativeLocalS6_eq_negative_fifth (gamma : ℝ) :
    nativeLocalHadamardMoment gamma 6 =
      -localLogDerivativeCoefficients
        (nativeLocalDeflatedCoefficient gamma) 5 := by
  norm_num [nativeLocalHadamardMoment, localHadamardMoment]

theorem nativeLocalS7_eq_sixth (gamma : ℝ) :
    nativeLocalHadamardMoment gamma 7 =
      localLogDerivativeCoefficients
        (nativeLocalDeflatedCoefficient gamma) 6 := by
  norm_num [nativeLocalHadamardMoment, localHadamardMoment]

/-- The same completed native characteristic supplies both the moments
used by the height operator and every local S_m readout. -/
theorem cameraGlobalAndLocalMoments_eq_native
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    completedNativeCameraLogDerivativeMoment camera cutoff =
      canonicalCompletedNativeLogDerivativeMoment ∧
    ∀ gamma m,
      cameraLocalHadamardMoment camera cutoff gamma m =
        nativeLocalHadamardMoment gamma m := by
  constructor
  · exact completedNativeCameraLogDerivativeMoment_eq_canonical hcamera cutoff
  · intro gamma m
    exact cameraLocalHadamardMoment_eq_native hcamera cutoff gamma m

theorem cameraLocalS6_eq_native
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff : ℕ) (gamma : ℝ) :
    cameraLocalHadamardMoment camera cutoff gamma 6 =
      nativeLocalHadamardMoment gamma 6 :=
  cameraLocalHadamardMoment_eq_native hcamera cutoff gamma 6

theorem cameraLocalS7_eq_native
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff : ℕ) (gamma : ℝ) :
    cameraLocalHadamardMoment camera cutoff gamma 7 =
      nativeLocalHadamardMoment gamma 7 :=
  cameraLocalHadamardMoment_eq_native hcamera cutoff gamma 7

end
end CarrySelfAdjointOperator

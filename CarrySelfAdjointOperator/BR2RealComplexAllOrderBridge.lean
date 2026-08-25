import CPFormal.Analytic.CpNativeCarryComplexOperatorSameAsReal
import NativeCarryC3Crosswalk.FinitePackaging
import NativeCarrySpectralWeyl.Camera.HigherDerivativeTail
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# All-order real--complex native camera bridge

The native camera is defined over the real plane.  Its complex expression is
the canonical continuous real-linear coordinate equivalence
`Complex.equivRealProdCLM.symm`.  This file records that the equivalence
commutes with every iterated real derivative and then combines that fact with
the existing finite-camera crosswalk and native-line chain rule.

No zero, cutoff limit, primality, scalar Green readout, or spectral hypothesis
is used.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- A continuous linear coordinate equivalence commutes with every iterated
derivative, including at points where differentiability is not supplied as a
separate premise. -/
theorem iteratedDeriv_continuousLinearEquiv_comp
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (f : ℝ → E) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun u => e (f u)) time =
      e (iteratedDeriv order f time) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv]
  change
    iteratedFDeriv ℝ order (e ∘ f) time (fun _ => 1) =
      e (iteratedFDeriv ℝ order f time (fun _ => 1))
  rw [e.iteratedFDeriv_comp_left]
  rfl

/-- For every camera, cutoff, derivative order, and real time, packaging the
real-plane derivative is exactly the derivative of the finite complex bracket
characteristic along the native line. -/
theorem packaged_iteratedDeriv_finiteNativeOperator_eq_along_nativeLine
    (camera cutoff order : ℕ) (time : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (iteratedDeriv order
          (fun u : ℝ => Operator.finiteNativeOperator camera cutoff u) time) =
      iteratedDeriv order
        (fun u : ℝ =>
          finiteBracketCharacteristic camera cutoff (nativeLine u)) time := by
  calc
    nativeCarryRealPlaneComplexPackaging
        (iteratedDeriv order
          (fun u : ℝ => Operator.finiteNativeOperator camera cutoff u) time) =
      iteratedDeriv order
        (fun u : ℝ =>
          nativeCarryRealPlaneComplexPackaging
            (Operator.finiteNativeOperator camera cutoff u)) time := by
        rw [nativeCarryRealPlaneComplexPackaging_eq_equivRealProdCLM_symm]
        exact (iteratedDeriv_continuousLinearEquiv_comp
          Complex.equivRealProdCLM.symm
          (fun u : ℝ => Operator.finiteNativeOperator camera cutoff u)
          order time).symm
    _ = iteratedDeriv order
        (fun u : ℝ =>
          finiteBracketCharacteristic camera cutoff (nativeLine u)) time := by
      congr 1
      funext u
      exact NativeCarryC3Crosswalk.packaged_finiteNativeOperator_eq_finiteBracketCharacteristic
        u camera cutoff

/-- The same all-order identity in complex analytic coordinates.  The sole
factor `I^order` is the already-proved rotation from real native time to the
complex parameter. -/
theorem packaged_iteratedDeriv_finiteNativeOperator_eq_complex
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff order : ℕ) (time : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (iteratedDeriv order
          (fun u : ℝ => Operator.finiteNativeOperator camera cutoff u) time) =
      iteratedDeriv order
          (finiteBracketCharacteristic camera cutoff) (nativeLine time) *
        Complex.I ^ order := by
  rw [packaged_iteratedDeriv_finiteNativeOperator_eq_along_nativeLine]
  exact iteratedDeriv_finiteBracketCharacteristic_along_nativeLine
    hcamera cutoff order time

/-- Unpacked form: the real-plane all-order jet is literally the pair of real
and imaginary coordinates of the rotated complex jet. -/
theorem iteratedDeriv_finiteNativeOperator_eq_complexCoordinates
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff order : ℕ) (time : ℝ) :
    iteratedDeriv order
        (fun u : ℝ => Operator.finiteNativeOperator camera cutoff u) time =
      Complex.equivRealProdCLM
        (iteratedDeriv order
            (finiteBracketCharacteristic camera cutoff) (nativeLine time) *
          Complex.I ^ order) := by
  have h := packaged_iteratedDeriv_finiteNativeOperator_eq_complex
    hcamera cutoff order time
  rw [nativeCarryRealPlaneComplexPackaging_eq_equivRealProdCLM_symm] at h
  calc
    iteratedDeriv order
        (fun u : ℝ => Operator.finiteNativeOperator camera cutoff u) time =
      Complex.equivRealProdCLM
        (Complex.equivRealProdCLM.symm
          (iteratedDeriv order
            (fun u : ℝ => Operator.finiteNativeOperator camera cutoff u)
            time)) :=
        (Complex.equivRealProdCLM.apply_symm_apply _).symm
    _ = Complex.equivRealProdCLM
        (iteratedDeriv order
            (finiteBracketCharacteristic camera cutoff) (nativeLine time) *
          Complex.I ^ order) := congrArg Complex.equivRealProdCLM h

/-! ## Exact head--tail completion in every order -/

/-- Package the real finite native jet and retain the exact analytic tail as a
separate summand.  The tail is rotated only after its complex derivative has
been taken, by the same `I^order` dictated by the native-line chain rule. -/
def completedPackagedFiniteNativeOperatorJet
    (camera cutoff order : ℕ) (time : ℝ) : ℂ :=
  nativeCarryRealPlaneComplexPackaging
      (iteratedDeriv order
        (fun u : ℝ => Operator.finiteNativeOperator camera cutoff u) time) +
    iteratedDeriv order
        (fun z : ℂ => bracketCharacteristic camera z -
          finiteBracketCharacteristic camera cutoff z)
        (nativeLine time) * Complex.I ^ order

/-- Exact all-order head--tail identity: the completed real native jet is the
cutoff-free bracket jet in complex coordinates. -/
theorem completedPackagedFiniteNativeOperatorJet_eq_complex
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff order : ℕ) (time : ℝ) :
    completedPackagedFiniteNativeOperatorJet camera cutoff order time =
      iteratedDeriv order (bracketCharacteristic camera) (nativeLine time) *
        Complex.I ^ order := by
  have hdomain : nativeLine time ∈ bracketDomain := by
    simp [bracketDomain]
    norm_num
  have hinfinite : ContDiffAt ℂ order (bracketCharacteristic camera)
      (nativeLine time) :=
    ((bracketCharacteristic_differentiableOn hcamera).contDiffOn
      isOpen_bracketDomain).contDiffAt
        (isOpen_bracketDomain.mem_nhds hdomain)
  have hfinite : ContDiffAt ℂ order
      (finiteBracketCharacteristic camera cutoff) (nativeLine time) :=
    (finiteBracketCharacteristic_differentiable hcamera cutoff).contDiff.contDiffAt
  unfold completedPackagedFiniteNativeOperatorJet
  rw [packaged_iteratedDeriv_finiteNativeOperator_eq_complex
    hcamera cutoff order time]
  change
    iteratedDeriv order (finiteBracketCharacteristic camera cutoff)
          (nativeLine time) * Complex.I ^ order +
        iteratedDeriv order
          (bracketCharacteristic camera -
            finiteBracketCharacteristic camera cutoff)
          (nativeLine time) * Complex.I ^ order =
      iteratedDeriv order (bracketCharacteristic camera) (nativeLine time) *
        Complex.I ^ order
  rw [iteratedDeriv_sub hinfinite hfinite]
  ring

/-- The same identity written entirely in the real native-time parameter. -/
theorem completedPackagedFiniteNativeOperatorJet_eq_along_nativeLine
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff order : ℕ) (time : ℝ) :
    completedPackagedFiniteNativeOperatorJet camera cutoff order time =
      iteratedDeriv order
        (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) time := by
  rw [completedPackagedFiniteNativeOperatorJet_eq_complex
      hcamera cutoff order time,
    iteratedDeriv_bracketCharacteristic_along_nativeLine hcamera]

/-- Exact completion removes the cutoff in every camera and derivative order;
this is an equality, not only an asymptotic tail estimate. -/
theorem completedPackagedFiniteNativeOperatorJet_cutoff_invariant
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (M N order : ℕ) (time : ℝ) :
    completedPackagedFiniteNativeOperatorJet camera M order time =
      completedPackagedFiniteNativeOperatorJet camera N order time := by
  rw [completedPackagedFiniteNativeOperatorJet_eq_complex
      hcamera M order time,
    completedPackagedFiniteNativeOperatorJet_eq_complex
      hcamera N order time]

end

end CarrySelfAdjointOperator

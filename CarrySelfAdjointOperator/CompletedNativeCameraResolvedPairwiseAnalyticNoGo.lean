import CarrySelfAdjointOperator.NativeCompletedCenteredReflection
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The complex-analytic obstruction for individual camera-pair Green responses

The fixed-atlas camera-pair expansion is an exact identity of functions.  It
must not, however, be differentiated pair by pair as complex functions along
the canonical one-variable response curve without first accounting for the
reflected source.  The existing direct-port extractor reads the fixed `w`
source, whereas the existing reflected-port extractor reads

`reflectedParameter (operatorHeightParameter u) =
 operatorHeightParameter (conj u)`.

Thus the moving port occurs in the *linear* (second) slot of `greenForm`, but
its parameter is anti-holomorphic in `u`.  This file proves the minimal local
no-go: that reflected parameter curve is not complex differentiable at the
center.  It does not assert that every individual pair kernel is nonanalytic:
a particular pair could vanish or enjoy an additional cancellation.  Rather,
it rules out the requested uniform port-wise `AnalyticAt` proof by composition
alone.

The full corrected response can still be complex analytic because its
non-Green channels cancel the anti-holomorphic dependence.  Its existing
Taylor jet therefore cannot be split into complex Taylor jets of the Green
pairs before that cancellation is retained.  The exact source-slot equations
remain the already compiled
`cameraResolvedDirectGreenPort_eq_reconstruction` and
`cameraResolvedReflectedGreenPort_eq_reconstruction`; this small module avoids
unfolding their large six-source reconstructions merely to restate them.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## The anti-holomorphic reflection curve -/

/-- Complex conjugation is real-linear but not complex differentiable at the
origin.  The proof compares its real derivative with the restriction of a
hypothetical complex-linear derivative on `1` and on `I`. -/
theorem complexConjugation_not_differentiableAt_zero :
    ¬ DifferentiableAt ℂ (fun u : ℂ => (starRingEnd ℂ) u) 0 := by
  intro h
  have hreal : DifferentiableAt ℝ (fun u : ℂ => (starRingEnd ℂ) u) 0 :=
    Complex.differentiable_conj.differentiableAt
  obtain ⟨g, hg⟩ := (differentiableAt_iff_restrictScalars ℝ hreal).mp h
  have hfderiv : fderiv ℝ (fun u : ℂ => (starRingEnd ℂ) u) 0 = Complex.conjCLE := by
    change fderiv ℝ (Complex.conjCLE : ℂ → ℂ) 0 = Complex.conjCLE
    exact Complex.conjCLE.fderiv
  have hmap : g.restrictScalars ℝ = Complex.conjCLE := by
    rw [hg]
    exact hfderiv
  have hone : g 1 = 1 := by
    have heval := DFunLike.congr_fun hmap (1 : ℂ)
    change g 1 = (↑Complex.conjCLE : ℂ →L[ℝ] ℂ) 1 at heval
    simpa [Complex.conjCLE_apply] using heval
  have hI : g Complex.I = -Complex.I := by
    have heval := DFunLike.congr_fun hmap Complex.I
    change g Complex.I = (↑Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I at heval
    simpa [Complex.conjCLE_apply] using heval
  have hlinear : g Complex.I = Complex.I * g 1 := by
    simpa only [smul_eq_mul, mul_one] using (g.map_smul Complex.I (1 : ℂ))
  have hcontradiction : Complex.I = -Complex.I := by
    calc
      Complex.I = Complex.I * g 1 := by rw [hone, mul_one]
      _ = g Complex.I := hlinear.symm
      _ = -Complex.I := hI
  have htwoI : (2 : ℂ) * Complex.I = 0 := by
    calc
      (2 : ℂ) * Complex.I = Complex.I - (-Complex.I) := by ring
      _ = 0 := sub_eq_zero.mpr hcontradiction
  exact Complex.I_ne_zero ((mul_eq_zero.mp htwoI).resolve_left (by norm_num))

/-- The direct height parametrization is affine, hence analytic at the Taylor
center.  This is the holomorphic half of the two parameter presentation. -/
theorem operatorHeightParameter_analyticAt_zero :
    AnalyticAt ℂ operatorHeightParameter 0 := by
  unfold operatorHeightParameter
  fun_prop

/-- The exact form of the reflected parameter along the canonical response
curve.  It is a conjugated, not a holomorphic, centered-height variable. -/
theorem reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj
    (u : ℂ) :
    reflectedParameter (operatorHeightParameter u) =
      operatorHeightParameter ((starRingEnd ℂ) u) :=
  (operatorHeightParameter_conj_eq_reflectedParameter u).symm

/-- The reflected parameter curve occurring in the camera-pair response is
not complex differentiable at the Taylor center. -/
theorem reflectedParameter_operatorHeightParameter_not_differentiableAt_zero :
    ¬ DifferentiableAt ℂ
      (fun u : ℂ => reflectedParameter (operatorHeightParameter u)) 0 := by
  intro h
  rw [show (fun u : ℂ => reflectedParameter (operatorHeightParameter u)) =
      fun u : ℂ => operatorHeightParameter ((starRingEnd ℂ) u) by
        funext u
        exact reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj u] at h
  have hsub : DifferentiableAt ℂ
      (fun u : ℂ => operatorHeightParameter ((starRingEnd ℂ) u) - (1 / 2 : ℂ)) 0 :=
    h.sub (differentiableAt_const (c := (1 / 2 : ℂ)))
  have hscaled := hsub.const_smul ((Complex.I)⁻¹)
  change DifferentiableAt ℂ
    (fun u : ℂ => Complex.I⁻¹ *
      (operatorHeightParameter ((starRingEnd ℂ) u) - (1 / 2 : ℂ))) 0 at hscaled
  have hfun :
      (fun u : ℂ => Complex.I⁻¹ *
        (operatorHeightParameter ((starRingEnd ℂ) u) - (1 / 2 : ℂ))) =
        fun u : ℂ => (starRingEnd ℂ) u := by
    funext u
    simp [operatorHeightParameter, Complex.inv_I, ← mul_assoc, Complex.I_mul_I]
  rw [hfun] at hscaled
  exact complexConjugation_not_differentiableAt_zero hscaled

/-- The same reflected curve cannot be analytic at the Taylor center. -/
theorem reflectedParameter_operatorHeightParameter_not_analyticAt_zero :
    ¬ AnalyticAt ℂ
      (fun u : ℂ => reflectedParameter (operatorHeightParameter u)) 0 := by
  intro h
  exact reflectedParameter_operatorHeightParameter_not_differentiableAt_zero
    h.differentiableAt

end

end CarrySelfAdjointOperator

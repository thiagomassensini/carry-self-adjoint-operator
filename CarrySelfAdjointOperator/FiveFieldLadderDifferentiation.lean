import CarrySelfAdjointOperator.FiveFieldLadderRecurrence
import Mathlib.Tactic

/-!
# Differentiating one finite ladder transition

This file gives the forward-mode derivative of the rational transition from
`FiveFieldLadderRecurrence`.  The input is a componentwise differentiable
family of six-field states.  The output derivative is written explicitly in
the same order `(R₀,R₁,R₂,r₀,r₁,r₂)`.

The hypotheses are precisely the non-vanishing hypotheses needed by the
divisions in the transition.  This is still a local algebraic statement: no
positivity, physical Riemann--Hilbert identification, or symplectic pullback
is asserted.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

def twoJumpLadderAlphaDerivative
    (_n : ℕ) (t1 t2 : ℂ) (_s ds : Fin 6 → ℂ) : ℂ :=
  -t1 * ds 1 - t2 * ds 2

def twoJumpLadderNextR1Derivative
    (n : ℕ) (t1 t2 : ℂ) (s ds : Fin 6 → ℂ) : ℂ :=
  -(twoJumpLadderAlphaDerivative n t1 t2 s ds) * s 1 +
    (t1 - twoJumpLadderAlpha n t1 t2 s) * ds 1 - ds 4

def twoJumpLadderNextR2Derivative
    (n : ℕ) (t1 t2 : ℂ) (s ds : Fin 6 → ℂ) : ℂ :=
  -(twoJumpLadderAlphaDerivative n t1 t2 s ds) * s 2 +
    (t2 - twoJumpLadderAlpha n t1 t2 s) * ds 2 - ds 5

def twoJumpLadderNextR0Derivative
    (n : ℕ) (t1 t2 : ℂ) (s ds : Fin 6 → ℂ) : ℂ :=
  twoJumpLadderNextR1Derivative n t1 t2 s ds +
    twoJumpLadderNextR2Derivative n t1 t2 s ds

def twoJumpLadderBetaDerivative
    (n : ℕ) (t1 t2 : ℂ) (s ds : Fin 6 → ℂ) : ℂ :=
  ((2 : ℂ) * twoJumpLadderNextR0 n t1 t2 s *
        twoJumpLadderNextR0Derivative n t1 t2 s ds * s 0 -
      (twoJumpLadderNextR0 n t1 t2 s) ^ 2 * ds 0) / (s 0) ^ 2 -
    ((2 : ℂ) * twoJumpLadderNextR1 n t1 t2 s *
        twoJumpLadderNextR1Derivative n t1 t2 s ds * s 1 -
      (twoJumpLadderNextR1 n t1 t2 s) ^ 2 * ds 1) / (s 1) ^ 2 -
    ((2 : ℂ) * twoJumpLadderNextR2 n t1 t2 s *
        twoJumpLadderNextR2Derivative n t1 t2 s ds * s 2 -
      (twoJumpLadderNextR2 n t1 t2 s) ^ 2 * ds 2) / (s 2) ^ 2

def twoJumpLadderNextR1ResidueDerivative
    (n : ℕ) (t1 t2 : ℂ) (s ds : Fin 6 → ℂ) : ℂ :=
  ((2 : ℂ) * twoJumpLadderNextR1 n t1 t2 s *
        twoJumpLadderNextR1Derivative n t1 t2 s ds *
        (twoJumpLadderBeta n t1 t2 s * s 1) -
      (twoJumpLadderNextR1 n t1 t2 s) ^ 2 *
        (twoJumpLadderBetaDerivative n t1 t2 s ds * s 1 +
          twoJumpLadderBeta n t1 t2 s * ds 1)) /
    (twoJumpLadderBeta n t1 t2 s * s 1) ^ 2

def twoJumpLadderNextR2ResidueDerivative
    (n : ℕ) (t1 t2 : ℂ) (s ds : Fin 6 → ℂ) : ℂ :=
  ((2 : ℂ) * twoJumpLadderNextR2 n t1 t2 s *
        twoJumpLadderNextR2Derivative n t1 t2 s ds *
        (twoJumpLadderBeta n t1 t2 s * s 2) -
      (twoJumpLadderNextR2 n t1 t2 s) ^ 2 *
        (twoJumpLadderBetaDerivative n t1 t2 s ds * s 2 +
          twoJumpLadderBeta n t1 t2 s * ds 2)) /
    (twoJumpLadderBeta n t1 t2 s * s 2) ^ 2

def twoJumpLadderStepDerivative
    (n : ℕ) (t1 t2 : ℂ) (s ds : Fin 6 → ℂ) : Fin 6 → ℂ :=
  ![twoJumpLadderNextR1ResidueDerivative n t1 t2 s ds +
      twoJumpLadderNextR2ResidueDerivative n t1 t2 s ds,
    twoJumpLadderNextR1ResidueDerivative n t1 t2 s ds,
    twoJumpLadderNextR2ResidueDerivative n t1 t2 s ds,
    twoJumpLadderNextR0Derivative n t1 t2 s ds,
    twoJumpLadderNextR1Derivative n t1 t2 s ds,
    twoJumpLadderNextR2Derivative n t1 t2 s ds]

theorem twoJumpLadderStep_hasDerivAt
    (n : ℕ) (t1 t2 : ℂ)
    (s : ℂ → Fin 6 → ℂ) (ds : Fin 6 → ℂ) (x : ℂ)
    (hs : ∀ i, HasDerivAt (fun y : ℂ => s y i) (ds i) x)
    (h0 : s x 0 ≠ 0) (h1 : s x 1 ≠ 0) (h2 : s x 2 ≠ 0)
    (hβ : twoJumpLadderBeta n t1 t2 (s x) ≠ 0) :
    HasDerivAt
      (fun y : ℂ => twoJumpLadderStep n t1 t2 (s y))
      (twoJumpLadderStepDerivative n t1 t2 (s x) ds) x := by
  let alpha : ℂ → ℂ := fun y => twoJumpLadderAlpha n t1 t2 (s y)
  let nr1 : ℂ → ℂ := fun y => twoJumpLadderNextR1 n t1 t2 (s y)
  let nr2 : ℂ → ℂ := fun y => twoJumpLadderNextR2 n t1 t2 (s y)
  let nr0 : ℂ → ℂ := fun y => twoJumpLadderNextR0 n t1 t2 (s y)
  let beta : ℂ → ℂ := fun y => twoJumpLadderBeta n t1 t2 (s y)
  let rr1 : ℂ → ℂ := fun y => twoJumpLadderNextR1Residue n t1 t2 (s y)
  let rr2 : ℂ → ℂ := fun y => twoJumpLadderNextR2Residue n t1 t2 (s y)
  have halpha : HasDerivAt alpha
      (twoJumpLadderAlphaDerivative n t1 t2 (s x) ds) x := by
    have hc := hasDerivAt_const x (((2 * n + 1 : ℕ) : ℂ))
    have h1' := (hs 1).const_mul t1
    have h2' := (hs 2).const_mul t2
    have h := (hc.sub h1').sub h2'
    convert! h using 1
    · simp [twoJumpLadderAlphaDerivative]
  have hnr1 : HasDerivAt nr1
      (twoJumpLadderNextR1Derivative n t1 t2 (s x) ds) x := by
    have hmul := ((hasDerivAt_const x t1).sub halpha).mul (hs 1)
    have h := hmul.sub (hs 4)
    convert! h using 1
    · simp [alpha, twoJumpLadderAlpha, twoJumpLadderNextR1Derivative]
  have hnr2 : HasDerivAt nr2
      (twoJumpLadderNextR2Derivative n t1 t2 (s x) ds) x := by
    have hmul := ((hasDerivAt_const x t2).sub halpha).mul (hs 2)
    have h := hmul.sub (hs 5)
    convert! h using 1
    · simp [alpha, twoJumpLadderAlpha, twoJumpLadderNextR2Derivative]
  have hnr0 : HasDerivAt nr0
      (twoJumpLadderNextR0Derivative n t1 t2 (s x) ds) x := by
    have hc := hasDerivAt_const x (-((n + 1 : ℕ) : ℂ))
    have h := (hc.add hnr1).add hnr2
    convert! h using 1
    · simp [twoJumpLadderNextR0Derivative]
  have hsq0 : HasDerivAt (fun y => nr0 y ^ 2)
      ((2 : ℂ) * nr0 x *
        twoJumpLadderNextR0Derivative n t1 t2 (s x) ds) x := by
    have h := hnr0.mul hnr0
    convert! h using 1
    · funext y
      simp [pow_two]
    · ring
  have hsq1 : HasDerivAt (fun y => nr1 y ^ 2)
      ((2 : ℂ) * nr1 x *
        twoJumpLadderNextR1Derivative n t1 t2 (s x) ds) x := by
    have h := hnr1.mul hnr1
    convert! h using 1
    · funext y
      simp [pow_two]
    · ring
  have hsq2 : HasDerivAt (fun y => nr2 y ^ 2)
      ((2 : ℂ) * nr2 x *
        twoJumpLadderNextR2Derivative n t1 t2 (s x) ds) x := by
    have h := hnr2.mul hnr2
    convert! h using 1
    · funext y
      simp [pow_two]
    · ring
  have hbeta : HasDerivAt beta
      (twoJumpLadderBetaDerivative n t1 t2 (s x) ds) x := by
    have hq0 := hsq0.div (hs 0) h0
    have hq1 := hsq1.div (hs 1) h1
    have hq2 := hsq2.div (hs 2) h2
    have h := (hq0.sub hq1).sub hq2
    convert! h using 1
  have hden1 : HasDerivAt (fun y => beta y * s y 1)
      (twoJumpLadderBetaDerivative n t1 t2 (s x) ds * s x 1 +
        beta x * ds 1) x := by
    have h := hbeta.mul (hs 1)
    convert! h using 1
  have hden2 : HasDerivAt (fun y => beta y * s y 2)
      (twoJumpLadderBetaDerivative n t1 t2 (s x) ds * s x 2 +
        beta x * ds 2) x := by
    have h := hbeta.mul (hs 2)
    convert! h using 1
  have hden1_ne : beta x * s x 1 ≠ 0 := mul_ne_zero hβ h1
  have hden2_ne : beta x * s x 2 ≠ 0 := mul_ne_zero hβ h2
  have hrr1 : HasDerivAt rr1
      (twoJumpLadderNextR1ResidueDerivative n t1 t2 (s x) ds) x := by
    have h := hsq1.div hden1 hden1_ne
    convert! h using 1
  have hrr2 : HasDerivAt rr2
      (twoJumpLadderNextR2ResidueDerivative n t1 t2 (s x) ds) x := by
    have h := hsq2.div hden2 hden2_ne
    convert! h using 1
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · have h := (hasDerivAt_const x (1 : ℂ)).add hrr1
    have h := h.add hrr2
    convert! h using 1
    · simp [twoJumpLadderStepDerivative]
  · exact hrr1
  · exact hrr2
  · exact hnr0
  · exact hnr1
  · exact hnr2

end

end NativeCarryFiveFieldCapstone

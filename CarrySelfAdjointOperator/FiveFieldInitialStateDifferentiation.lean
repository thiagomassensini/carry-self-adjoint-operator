import CarrySelfAdjointOperator.FiveFieldTangentWitnessBridge
import Mathlib.Tactic

/-!
# First finite-state differentiation layer

This is the `n = 0` layer of the finite recurrence used by the numerical
operator audit. It makes the parameter dependence explicit and proves the
two amplitude derivatives of the initial normalized state. The recursive
`n > 0` ladder and the logarithmic native coordinates are intentionally left
for the next bridge; no analytic family is identified by a name alone.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

def twoJumpInitialHeight (t1 t2 a1 a2 : ℂ) : ℂ :=
  1 + a1 * Complex.exp (-t1) + a2 * Complex.exp (-t2)

def twoJumpInitialR1 (t1 t2 a1 a2 : ℂ) : ℂ :=
  (-a1 * Complex.exp (-t1)) / twoJumpInitialHeight t1 t2 a1 a2

def twoJumpInitialR2 (t1 t2 a1 a2 : ℂ) : ℂ :=
  (-a2 * Complex.exp (-t2)) / twoJumpInitialHeight t1 t2 a1 a2

/-- The six entries are `(R0,R1,R2,r0,r1,r2)` at ladder level zero. -/
def twoJumpInitialState (t1 t2 a1 a2 : ℂ) : Fin 6 → ℂ :=
  ![1 + twoJumpInitialR1 t1 t2 a1 a2 + twoJumpInitialR2 t1 t2 a1 a2,
    twoJumpInitialR1 t1 t2 a1 a2, twoJumpInitialR2 t1 t2 a1 a2,
    0, 0, 0]

def twoJumpInitialStateC1Derivative (t1 t2 a1 a2 : ℂ) : Fin 6 → ℂ :=
  let e1 := Complex.exp (-t1)
  let e2 := Complex.exp (-t2)
  let h := twoJumpInitialHeight t1 t2 a1 a2
  let dh := e1
  let n1 := -a1 * e1
  let n2 := -a2 * e2
  let dr1 := ((-e1) * h - n1 * dh) / h ^ 2
  let dr2 := (0 * h - n2 * dh) / h ^ 2
  ![dr1 + dr2, dr1, dr2, 0, 0, 0]

def twoJumpInitialStateC2Derivative (t1 t2 a1 a2 : ℂ) : Fin 6 → ℂ :=
  let e1 := Complex.exp (-t1)
  let e2 := Complex.exp (-t2)
  let h := twoJumpInitialHeight t1 t2 a1 a2
  let dh := e2
  let n1 := -a1 * e1
  let n2 := -a2 * e2
  let dr1 := (0 * h - n1 * dh) / h ^ 2
  let dr2 := ((-e2) * h - n2 * dh) / h ^ 2
  ![dr1 + dr2, dr1, dr2, 0, 0, 0]

theorem twoJumpInitialState_hasDerivAt_c1
    (t1 t2 a1 a2 : ℂ)
    (hh : twoJumpInitialHeight t1 t2 a1 a2 ≠ 0) :
    HasDerivAt (fun a => twoJumpInitialState t1 t2 a a2)
      (twoJumpInitialStateC1Derivative t1 t2 a1 a2) a1 := by
  let e1 : ℂ := Complex.exp (-t1)
  let e2 : ℂ := Complex.exp (-t2)
  have hheight : HasDerivAt
      (fun a : ℂ => twoJumpInitialHeight t1 t2 a a2) e1 a1 := by
    convert! (((hasDerivAt_id a1).mul_const e1).add_const (1 + a2 * e2)) using 1
    · funext x
      simp [twoJumpInitialHeight, e1, e2]
      ring
    · simp
  have hnum1 : HasDerivAt (fun a : ℂ => -a * e1) (-e1) a1 := by
    convert! (hasDerivAt_id a1).neg.mul_const e1 using 1
    ring
  have hnum2 : HasDerivAt (fun _ : ℂ => -a2 * e2) 0 a1 :=
    hasDerivAt_const a1 _
  have hr1 := hnum1.div hheight hh
  have hr2 := hnum2.div hheight hh
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! (hr1.add hr2).add_const (1 : ℂ) using 1
    · funext x
      simp [twoJumpInitialState, twoJumpInitialR1, twoJumpInitialR2,
        twoJumpInitialHeight, e1, e2]
      ring
  · convert! hr1 using 1
  · convert! hr2 using 1
  · change HasDerivAt (fun _ : ℂ => (0 : ℂ)) 0 a1
    exact hasDerivAt_const a1 0
  · change HasDerivAt (fun _ : ℂ => (0 : ℂ)) 0 a1
    exact hasDerivAt_const a1 0
  · change HasDerivAt (fun _ : ℂ => (0 : ℂ)) 0 a1
    exact hasDerivAt_const a1 0

theorem twoJumpInitialState_hasDerivAt_c2
    (t1 t2 a1 a2 : ℂ)
    (hh : twoJumpInitialHeight t1 t2 a1 a2 ≠ 0) :
    HasDerivAt (fun a => twoJumpInitialState t1 t2 a1 a)
      (twoJumpInitialStateC2Derivative t1 t2 a1 a2) a2 := by
  let e1 : ℂ := Complex.exp (-t1)
  let e2 : ℂ := Complex.exp (-t2)
  have hheight : HasDerivAt
      (fun a : ℂ => twoJumpInitialHeight t1 t2 a1 a) e2 a2 := by
    convert! (((hasDerivAt_id a2).mul_const e2).add_const (1 + a1 * e1)) using 1
    · funext x
      simp [twoJumpInitialHeight, e1, e2]
      ring
    · simp
  have hnum1 : HasDerivAt (fun _ : ℂ => -a1 * e1) 0 a2 :=
    hasDerivAt_const a2 _
  have hnum2 : HasDerivAt (fun a : ℂ => -a * e2) (-e2) a2 := by
    convert! (hasDerivAt_id a2).neg.mul_const e2 using 1
    ring
  have hr1 := hnum1.div hheight hh
  have hr2 := hnum2.div hheight hh
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! (hr1.add hr2).add_const (1 : ℂ) using 1
    · funext x
      simp [twoJumpInitialState, twoJumpInitialR1, twoJumpInitialR2,
        twoJumpInitialHeight, e1, e2]
      ring
  · convert! hr1 using 1
  · convert! hr2 using 1
  · change HasDerivAt (fun _ : ℂ => (0 : ℂ)) 0 a2
    exact hasDerivAt_const a2 0
  · change HasDerivAt (fun _ : ℂ => (0 : ℂ)) 0 a2
    exact hasDerivAt_const a2 0
  · change HasDerivAt (fun _ : ℂ => (0 : ℂ)) 0 a2
    exact hasDerivAt_const a2 0

end

end NativeCarryFiveFieldCapstone

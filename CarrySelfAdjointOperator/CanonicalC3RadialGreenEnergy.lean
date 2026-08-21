import CarrySelfAdjointOperator.CanonicalC3GreenIntertwiner
import Mathlib.Tactic

/-!
# Canonical radial C3 energy in the diagonal Wronskian normalization

A diagonal scalar Green Wronskian is always purely imaginary.  The raw
direct/reflected C3 Green bulk is not: away from the critical line its real
part is the nonzero radial carry defect times a strictly positive reflected
gradient pairing.  Consequently the raw complex bulk cannot itself be the
global diagonal Wronskian scalarization.

The compatible scalar is obtained without discarding the detector.  Writing

`delta = re(s) - 1/2`,

the exact factorization

`cpRadialDifference 3 delta = 2 * delta * cpRadialCofactor 3 delta`

turns the real part of the C3 bulk into the positive radial energy

`2 * cpRadialCofactor 3 delta * re(reflectedGradientPairing)`.

In centered height coordinates `delta = -im(z)`, and multiplication by
`z - conj z` recovers exactly `-2 i` times the real C3 bulk.  This is the
normalization compatible with the already constructed realified gamma/Cauchy
identity.  The remaining analytic statement is therefore an equality of two
purely imaginary scalars, not an equality with the raw complex C3 form.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Every diagonal scalar Wronskian has zero real part. -/
theorem completedGreenWronskian_diagonal_re_eq_zero
    (F Psi : ℂ → ℂ) (z : ℂ) :
    (completedGreenWronskian F Psi z z).re = 0 := by
  simp [completedGreenWronskian, Complex.mul_re]
  ring

/-- The real part of the canonical C3 bulk retains the exact radial defect
and the strictly positive reflected-gradient channel. -/
theorem canonicalEnrichedC3ReflectedGreenBulk_re_eq_radialFactorization
    (s : ℂ) :
    (canonicalEnrichedC3ReflectedGreenBulk s).re =
      cpRadialDifference 3 (criticalDisplacement s.re) *
        (finiteReflectedGradientPairing 3 s).re := by
  rw [canonicalEnrichedC3ReflectedGreenBulk_eq_radialFactorization]
  simp [Complex.mul_re]

/-- In the open strip, already the real part of the raw C3 bulk vanishes
exactly on the critical line. -/
theorem canonicalEnrichedC3ReflectedGreenBulk_re_eq_zero_iff_re_eq_half
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (canonicalEnrichedC3ReflectedGreenBulk s).re = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [canonicalEnrichedC3ReflectedGreenBulk_re_eq_radialFactorization]
  constructor
  · intro hzero
    have hpairing : (finiteReflectedGradientPairing 3 s).re ≠ 0 :=
      ne_of_gt (finiteReflectedGradientPairing_re_pos (by norm_num) hs)
    have hradial :
        cpRadialDifference 3 (criticalDisplacement s.re) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hpairing
    have hcritical : criticalDisplacement s.re = 0 :=
      (cpRadialDifference_eq_zero_iff
        3 (by norm_num) (criticalDisplacement s.re)).1 hradial
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    have hcritical : criticalDisplacement s.re = 0 := by
      unfold criticalDisplacement
      linarith
    rw [hcritical]
    simp [cpRadialDifference]

/-- Exact type-level diagnosis of the former raw scalar intertwiner: off the
critical line a diagonal Wronskian cannot equal the raw complex C3 bulk,
regardless of the scalar functions used to form that Wronskian. -/
theorem completedDiagonalWronskian_ne_canonicalEnrichedC3ReflectedGreenBulk
    (F Psi : ℂ → ℂ) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    completedGreenWronskian F Psi
        (centeredHeightParameter s) (centeredHeightParameter s) ≠
      canonicalEnrichedC3ReflectedGreenBulk s := by
  intro heq
  have hbulkRe : (canonicalEnrichedC3ReflectedGreenBulk s).re = 0 := by
    rw [← heq]
    exact completedGreenWronskian_diagonal_re_eq_zero
      F Psi (centeredHeightParameter s)
  exact hoff
    ((canonicalEnrichedC3ReflectedGreenBulk_re_eq_zero_iff_re_eq_half hs).1
      hbulkRe)

/-- The globally quantified raw complex C3 scalar intertwiner is formally
impossible.  This no-go concerns only that premature scalar projection; it
does not concern the realified gamma/Cauchy energy route. -/
theorem not_hasCanonicalEnrichedC3DiagonalGreenIntertwiner :
    ¬ HasCanonicalEnrichedC3DiagonalGreenIntertwiner := by
  intro hintertwiner
  let s : ℂ := ((3 / 4 : ℝ) : ℂ)
  let z : ℂ := centeredHeightParameter s
  have hs : s ∈ genuineCriticalStrip := by
    constructor <;> norm_num [s]
  have hoff : s.re ≠ (1 : ℝ) / 2 := by
    norm_num [s]
  have hz : z.im ≠ 0 := by
    simp [z, s]
  have hne :=
    completedDiagonalWronskian_ne_canonicalEnrichedC3ReflectedGreenBulk
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion hs hoff
  apply hne
  simpa [z] using hintertwiner z hz

/-- Positive real C3 energy obtained by dividing the odd radial defect by
its centered displacement through the already-defined continuous cofactor.
No division occurs in the definition. -/
def canonicalC3RadialGreenEnergy (s : ℂ) : ℝ :=
  2 * cpRadialCofactor 3 (criticalDisplacement s.re) *
    (finiteReflectedGradientPairing 3 s).re

/-- The canonical radial C3 energy is strictly positive throughout the open
strip, including on the critical line where the cofactor supplies the
continuous value. -/
theorem canonicalC3RadialGreenEnergy_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < canonicalC3RadialGreenEnergy s := by
  unfold canonicalC3RadialGreenEnergy
  exact mul_pos
    (mul_pos (by norm_num)
      (cpRadialCofactor_pos 3 (by norm_num) (criticalDisplacement s.re)))
    (finiteReflectedGradientPairing_re_pos (by norm_num) hs)

/-- In centered height coordinates, the critical displacement is exactly the
negative imaginary part of the operator parameter. -/
@[simp] theorem criticalDisplacement_operatorHeightParameter (z : ℂ) :
    criticalDisplacement (operatorHeightParameter z).re = -z.im := by
  simp [criticalDisplacement, operatorHeightParameter, Complex.mul_re]
  ring

/-- Real normalization identity: multiplying the positive C3 radial energy
by `im(z)` recovers minus the real part of the raw C3 bulk. -/
theorem operatorHeight_im_mul_canonicalC3RadialGreenEnergy
    (z : ℂ) :
    z.im * canonicalC3RadialGreenEnergy (operatorHeightParameter z) =
      -(canonicalEnrichedC3ReflectedGreenBulk
          (operatorHeightParameter z)).re := by
  rw [canonicalEnrichedC3ReflectedGreenBulk_re_eq_radialFactorization,
    cpRadialDifference_eq_two_mul_delta_mul_cofactor]
  unfold canonicalC3RadialGreenEnergy
  rw [criticalDisplacement_operatorHeightParameter]
  ring

/-- Complex normalization compatible with a diagonal Green Wronskian and
with the existing `-2 i * CauchySkew` gamma scalarization. -/
theorem centeredHeightFactor_mul_canonicalC3RadialGreenEnergy
    (z : ℂ) :
    (z - (starRingEnd ℂ) z) *
        (canonicalC3RadialGreenEnergy
          (operatorHeightParameter z) : ℂ) =
      (-(2 : ℂ) * Complex.I) *
        ((canonicalEnrichedC3ReflectedGreenBulk
          (operatorHeightParameter z)).re : ℂ) := by
  have hreal := operatorHeight_im_mul_canonicalC3RadialGreenEnergy z
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
    linarith

/-- Corrected strip-local diagonal C3 identity.  Both sides are now purely
imaginary, and the right side uses a strictly positive real energy. -/
def HasCanonicalC3RadialDiagonalGreenIdentity : Prop :=
  ∀ z : ℂ, operatorHeightParameter z ∈ genuineCriticalStrip →
    z.im ≠ 0 →
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z =
        (z - (starRingEnd ℂ) z) *
          (canonicalC3RadialGreenEnergy
            (operatorHeightParameter z) : ℂ)

/-- The corrected radial-energy identity would close every open-strip zeta
zero, with nonvanishing discharged by strict positivity of the C3 energy. -/
theorem riemannZeta_zero_re_eq_half_of_canonicalC3RadialGreenIdentity
    (hgreen : HasCanonicalC3RadialDiagonalGreenIdentity)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0) :
    s.re = (1 : ℝ) / 2 := by
  by_contra hoff
  let z : ℂ := centeredHeightParameter s
  have hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip := by
    simpa [z] using hs
  have hzIm : z.im ≠ 0 := by
    dsimp [z]
    rw [centeredHeightParameter_im]
    intro him
    apply hoff
    linarith
  have hcharacteristic :
      completedNativeOperatorCharacteristic z = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta]
    · simp [z, hzero]
    · exact hzStrip
  have hwronskian :
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z = 0 := by
    simp [completedGreenWronskian, hcharacteristic]
  have hidentity := hgreen z hzStrip hzIm
  rw [hwronskian] at hidentity
  have henergy :
      canonicalC3RadialGreenEnergy (operatorHeightParameter z) ≠ 0 :=
    ne_of_gt (canonicalC3RadialGreenEnergy_pos hzStrip)
  have henergyComplex :
      (canonicalC3RadialGreenEnergy
        (operatorHeightParameter z) : ℂ) ≠ 0 := by
    exact_mod_cast henergy
  have hfixed : z = (starRingEnd ℂ) z := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hidentity.symm).resolve_right henergyComplex
  have him := congrArg Complex.im hfixed
  simp only [Complex.conj_im] at him
  exact hzIm (by linarith)

end

end CarrySelfAdjointOperator

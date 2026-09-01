import CarrySelfAdjointOperator.CompletedNativeCentralChiralQuotientCurvature
import Mathlib.Tactic

/-!
# Cayley--Herglotz form of the completed-native chiral gate

The completed Hermite--Biehler quotient is the Cayley transform of the
negative logarithmic derivative

`a(z) = -F'(z) / F(z)`:

`q(z) = (a(z) - i) / (a(z) + i)`.

On every regular pair, its Pick kernel is therefore exactly

`P_q(z,w) = 2 * conj(c(z)) * K_a(z,w) * c(w)`,

where `c(z) = (a(z) + i)⁻¹` and

`K_a(z,w) = (a(w) - conj(a(z))) / (w - conj z)`.

Thus finite Pick positivity is equivalent, not merely implied by, positivity
of the Herglotz kernel of `-F'/F`.  This module identifies the remaining
all-order gate; it does not assume or prove that the logarithmic derivative
is a Herglotz function.
-/

open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace CarrySelfAdjointOperator

open Filter

noncomputable section

/-! ## Scalar Cayley factorization -/

/-- Negative logarithmic derivative of the completed-native characteristic.
It is the candidate Herglotz coordinate underlying the chiral quotient. -/
def completedNativeLogDerivativeHerglotzCoordinate (z : ℂ) : ℂ :=
  -deriv completedNativeOperatorCharacteristic z /
    completedNativeOperatorCharacteristic z

/-- The Cayley/Herglotz notation is definitionally the already globalized
completed-native operator logarithmic derivative. -/
@[simp] theorem completedNativeLogDerivativeHerglotzCoordinate_eq_operatorLogDerivative
    (z : ℂ) :
    completedNativeLogDerivativeHerglotzCoordinate z =
      completedNativeOperatorLogDerivative z :=
  rfl

/-- Centered evenness makes the logarithmic-derivative coordinate vanish. -/
@[simp] theorem completedNativeLogDerivativeHerglotzCoordinate_zero :
    completedNativeLogDerivativeHerglotzCoordinate 0 = 0 := by
  unfold completedNativeLogDerivativeHerglotzCoordinate
  rw [deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
    completedNativeOperatorCharacteristic_eventually_even]
  simp

/-- The first Herglotz-coordinate jet is the characteristic curvature:
`a'(0) = 2 h₀`.  Thus the second derivative of `F` is precisely the first
local ruler seen by the Cayley/Pick gate. -/
theorem hasDerivAt_completedNativeLogDerivativeHerglotzCoordinate_zero :
    HasDerivAt completedNativeLogDerivativeHerglotzCoordinate
      (2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) 0 := by
  have hF :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.hasDerivAt
  have hFzero : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  have hderiv :
      HasDerivAt (deriv completedNativeOperatorCharacteristic)
        (iteratedDeriv 2 completedNativeOperatorCharacteristic 0) 0 := by
    have h :=
      (completedNativeOperatorCharacteristic_analyticAt
        zero_mem_completedNativeHeightDomain).deriv.differentiableAt.hasDerivAt
    simpa [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ] using h
  have hquot := hderiv.neg.div hF
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hm :=
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral
  change HasDerivAt
    (fun z => -deriv completedNativeOperatorCharacteristic z /
      completedNativeOperatorCharacteristic z)
    ((-iteratedDeriv 2 completedNativeOperatorCharacteristic 0 *
          completedNativeOperatorCharacteristic 0 -
        (-deriv completedNativeOperatorCharacteristic 0) *
          deriv completedNativeOperatorCharacteristic 0) /
      completedNativeOperatorCharacteristic 0 ^ 2) 0 at hquot
  rw [hFzero] at hquot
  simp only [neg_zero, zero_mul, sub_zero] at hquot
  change HasDerivAt
    (fun z => -deriv completedNativeOperatorCharacteristic z /
      completedNativeOperatorCharacteristic z)
    (2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) 0
  rw [hm]
  convert hquot using 1
  have hFne := completedNativeOperatorCharacteristic_zero_ne_zero
  field_simp [hFne]

/-- The positive Hermite--Biehler coordinate is `F * (a + i)` wherever the
characteristic is nonzero. -/
theorem completedNativePositiveHermiteBiehlerCoordinate_eq_characteristic_mul_herglotz_add_I
    {z : ℂ}
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativePositiveHermiteBiehlerCoordinate z =
      completedNativeOperatorCharacteristic z *
        (completedNativeLogDerivativeHerglotzCoordinate z + Complex.I) := by
  unfold completedNativePositiveHermiteBiehlerCoordinate
    completedNativeLogDerivativeHerglotzCoordinate
  field_simp [hF]

/-- The negative Hermite--Biehler coordinate is `F * (a - i)` wherever the
characteristic is nonzero. -/
theorem completedNativeNegativeHermiteBiehlerCoordinate_eq_characteristic_mul_herglotz_sub_I
    {z : ℂ}
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeNegativeHermiteBiehlerCoordinate z =
      completedNativeOperatorCharacteristic z *
        (completedNativeLogDerivativeHerglotzCoordinate z - Complex.I) := by
  unfold completedNativeNegativeHermiteBiehlerCoordinate
    completedNativeLogDerivativeHerglotzCoordinate
  field_simp [hF]

/-- The canonical chiral quotient is the Cayley transform of `-F'/F`. -/
theorem completedNativeHermiteBiehlerChiralQuotient_eq_cayley
    {z : ℂ}
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeHermiteBiehlerChiralQuotient z =
      (completedNativeLogDerivativeHerglotzCoordinate z - Complex.I) /
        (completedNativeLogDerivativeHerglotzCoordinate z + Complex.I) := by
  unfold completedNativeHermiteBiehlerChiralQuotient
  rw [
    completedNativeNegativeHermiteBiehlerCoordinate_eq_characteristic_mul_herglotz_sub_I
      hF,
    completedNativePositiveHermiteBiehlerCoordinate_eq_characteristic_mul_herglotz_add_I
      hF]
  exact mul_div_mul_left _ _ hF

/-- Divided-difference kernel whose positivity is the Herglotz/Nevanlinna
condition for the negative logarithmic derivative. -/
def completedNativeLogDerivativeHerglotzKernel (z w : ℂ) : ℂ :=
  (completedNativeLogDerivativeHerglotzCoordinate w -
      conj (completedNativeLogDerivativeHerglotzCoordinate z)) /
    (w - conj z)

/-- Diagonal Cayley amplitude relating the Herglotz and Pick kernels. -/
def completedNativeCayleyHerglotzAmplitude (z : ℂ) : ℂ :=
  (completedNativeLogDerivativeHerglotzCoordinate z + Complex.I)⁻¹

/-- Nonvanishing of the positive Hermite--Biehler coordinate makes the
Cayley amplitude nonzero. -/
theorem completedNativeCayleyHerglotzAmplitude_ne_zero
    {z : ℂ}
    (hF : completedNativeOperatorCharacteristic z ≠ 0)
    (hpositive : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0) :
    completedNativeCayleyHerglotzAmplitude z ≠ 0 := by
  unfold completedNativeCayleyHerglotzAmplitude
  apply inv_ne_zero
  intro hzero
  apply hpositive
  rw [
    completedNativePositiveHermiteBiehlerCoordinate_eq_characteristic_mul_herglotz_add_I
      hF,
    hzero, mul_zero]

/-- Exact scalar Cayley identity: the chiral Pick kernel is a diagonally
weighted copy of the Herglotz kernel of `-F'/F`. -/
theorem completedNativeHermiteBiehlerChiralPickKernel_eq_cayleyHerglotz
    {z w : ℂ}
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z)
    (hzPositive : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0)
    (hwPositive : completedNativePositiveHermiteBiehlerCoordinate w ≠ 0) :
    completedNativeHermiteBiehlerChiralPickKernel z w =
      2 * conj (completedNativeCayleyHerglotzAmplitude z) *
        completedNativeLogDerivativeHerglotzKernel z w *
          completedNativeCayleyHerglotzAmplitude w := by
  let az := completedNativeLogDerivativeHerglotzCoordinate z
  let aw := completedNativeLogDerivativeHerglotzCoordinate w
  have hzPlus : az + Complex.I ≠ 0 := by
    intro hzero
    apply hzPositive
    rw [
      completedNativePositiveHermiteBiehlerCoordinate_eq_characteristic_mul_herglotz_add_I
        hzF]
    change completedNativeOperatorCharacteristic z * (az + Complex.I) = 0
    rw [hzero, mul_zero]
  have hwPlus : aw + Complex.I ≠ 0 := by
    intro hzero
    apply hwPositive
    rw [
      completedNativePositiveHermiteBiehlerCoordinate_eq_characteristic_mul_herglotz_add_I
        hwF]
    change completedNativeOperatorCharacteristic w * (aw + Complex.I) = 0
    rw [hzero, mul_zero]
  have hzConjPlus : conj az - Complex.I ≠ 0 := by
    have hmap := (map_ne_zero (starRingEnd ℂ)).2 hzPlus
    simpa only [map_add, Complex.conj_I, sub_eq_add_neg] using hmap
  have hzConjPlus' : conj az + -Complex.I ≠ 0 := by
    simpa only [sub_eq_add_neg] using hzConjPlus
  unfold completedNativeHermiteBiehlerChiralPickKernel
  rw [completedNativeHermiteBiehlerChiralQuotient_eq_cayley hzF,
    completedNativeHermiteBiehlerChiralQuotient_eq_cayley hwF]
  unfold completedNativeLogDerivativeHerglotzKernel
    completedNativeCayleyHerglotzAmplitude
  change
    Complex.I *
        (1 - conj ((az - Complex.I) / (az + Complex.I)) *
          ((aw - Complex.I) / (aw + Complex.I))) /
          (w - conj z) =
      2 * conj ((az + Complex.I)⁻¹) *
        ((aw - conj az) / (w - conj z)) * (aw + Complex.I)⁻¹
  simp only [map_div₀, map_sub, map_add, map_inv₀, Complex.conj_I]
  field_simp [hsep, hzPlus, hwPlus, hzConjPlus']
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Finite radial equivalence -/

/-- Radial sample matrix of the Herglotz kernel on the canonical shrinking
upper-half-plane grid. -/
def canonicalCompletedNativeRadialHerglotzSampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    completedNativeLogDerivativeHerglotzKernel
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)

/-- On a regular radial section, the Pick matrix is twice the diagonal
congruence of the logarithmic-derivative Herglotz matrix. -/
theorem canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_herglotzCongruence
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
        completedNativePositiveHermiteBiehlerCoordinate
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    canonicalCompletedNativeRadialChiralPickSampleMatrix k N =
      (2 : ℝ) •
        (Matrix.conjTranspose
              (Matrix.diagonal (fun i : Fin N =>
                completedNativeCayleyHerglotzAmplitude
                  (canonicalCompletedC3RadialTiltPoint k i))) *
            canonicalCompletedNativeRadialHerglotzSampleMatrix k N *
          Matrix.diagonal (fun i : Fin N =>
            completedNativeCayleyHerglotzAmplitude
              (canonicalCompletedC3RadialTiltPoint k i))) := by
  ext i j
  unfold canonicalCompletedNativeRadialChiralPickSampleMatrix
  simp only [Matrix.of_apply]
  rw [completedNativeHermiteBiehlerChiralPickKernel_eq_cayleyHerglotz
    (hregular i).1 (hregular j).1
    (sub_ne_zero.mp
      (canonicalCompletedC3RadialTilt_separation_ne_zero k i j))
    (hregular i).2 (hregular j).2]
  simp [canonicalCompletedNativeRadialHerglotzSampleMatrix]
  ring

/-- The regular radial Pick matrix and the Herglotz matrix have exactly the
same positive-semidefinite status. -/
theorem canonicalCompletedNativeRadialChiralPickSampleMatrix_posSemidef_iff_herglotz
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
        completedNativePositiveHermiteBiehlerCoordinate
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (canonicalCompletedNativeRadialChiralPickSampleMatrix k N).PosSemidef ↔
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k N).PosSemidef := by
  rw [canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_herglotzCongruence
    k N hregular]
  let amplitude : Fin N → ℂ := fun i =>
    completedNativeCayleyHerglotzAmplitude
      (canonicalCompletedC3RadialTiltPoint k i)
  let congruence : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.conjTranspose (Matrix.diagonal amplitude) *
      canonicalCompletedNativeRadialHerglotzSampleMatrix k N *
        Matrix.diagonal amplitude
  have hamplitude : ∀ i, amplitude i ≠ 0 := fun i =>
    completedNativeCayleyHerglotzAmplitude_ne_zero
      (hregular i).1 (hregular i).2
  have hcongruence : congruence.PosSemidef ↔
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k N).PosSemidef := by
    exact diagonal_congruence_posSemidef_iff amplitude hamplitude _
  constructor
  · intro hscaled
    have hhalf := hscaled.smul (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by positivity)
    have hcongruencePos : congruence.PosSemidef := by
      simpa [congruence, amplitude, smul_smul] using hhalf
    exact hcongruence.mp hcongruencePos
  · intro hHerglotz
    have hcongruencePos : congruence.PosSemidef :=
      hcongruence.mpr hHerglotz
    simpa [congruence, amplitude] using
      hcongruencePos.smul (show (0 : ℝ) ≤ 2 by norm_num)

/-- Eventual finite-section positivity of the radial Herglotz kernel.  This
is a named gate, not an assumption hidden in the Cayley algebra. -/
def CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite : Prop :=
  ∀ N : ℕ, ∀ᶠ k : ℕ in atTop,
    (canonicalCompletedNativeRadialHerglotzSampleMatrix k N).PosSemidef

/-- Eventual radial Herglotz positivity is exactly the previously isolated
radial Pick gate. -/
theorem canonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite_iff_pick :
    CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite ↔
      CanonicalCompletedNativeRadialChiralPickEventuallyPosSemidefinite := by
  constructor
  · intro hHerglotz N
    have hregular : ∀ᶠ k : ℕ in atTop, ∀ i : Fin N,
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
      rw [Filter.eventually_all]
      intro i
      filter_upwards [
        (canonicalCompletedC3RadialTiltPoint_tendsto_zero i).eventually
          completedNativeChiralPickFactorization_eventually_regular] with k hk
      exact ⟨hk.2.1, hk.2.2⟩
    filter_upwards [hHerglotz N, hregular] with k hk hreg
    exact
      (canonicalCompletedNativeRadialChiralPickSampleMatrix_posSemidef_iff_herglotz
        k N hreg).mpr hk
  · intro hPick N
    have hregular : ∀ᶠ k : ℕ in atTop, ∀ i : Fin N,
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
      rw [Filter.eventually_all]
      intro i
      filter_upwards [
        (canonicalCompletedC3RadialTiltPoint_tendsto_zero i).eventually
          completedNativeChiralPickFactorization_eventually_regular] with k hk
      exact ⟨hk.2.1, hk.2.2⟩
    filter_upwards [hPick N, hregular] with k hk hreg
    exact
      (canonicalCompletedNativeRadialChiralPickSampleMatrix_posSemidef_iff_herglotz
        k N hreg).mp hk

/-- Final gate spelling: all-order contractivity of the concrete chiral
multiplier is precisely eventual positivity of the logarithmic-derivative
Herglotz kernel. -/
theorem canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_herglotz :
    CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive ↔
      CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite := by
  rw [canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_pick,
    canonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite_iff_pick]

/-- The Herglotz spelling reaches the closed completed-native moment forms
without passing through an unnamed positivity premise. -/
theorem canonicalCompletedNativeStieltjesPosSemidefinite_of_radialHerglotz
    (hHerglotz :
      CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite) :
    CanonicalCompletedNativeStieltjesPosSemidefinite :=
  canonicalCompletedNativeStieltjesPosSemidefinite_of_radialChiralMultiplier
    (canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_herglotz.mpr
      hHerglotz)

/-- Conditional endpoint in Herglotz language: eventual positivity of every
radial logarithmic-derivative kernel section, together with the separately
isolated finite-section nondegeneracy, implies zero confinement. -/
theorem completedNativeOperator_zero_im_eq_zero_of_radialHerglotz
    (hHerglotz :
      CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_radialChiralMultiplier
    (canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_herglotz.mpr
      hHerglotz)
    hnondegenerate hzDomain hzero

end

end CarrySelfAdjointOperator

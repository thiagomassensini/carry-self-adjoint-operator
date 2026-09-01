import CarrySelfAdjointOperator.CompletedNativeRadialChiralMultiplier
import Mathlib.Tactic

/-!
# Projective chiral carrier for the completed-native divided slope

The raw ambient response is a positive Gram, but its normalization does not
realize the completed-native moment kernel.  The exact chiral factorization
identifies the missing transformation:

* the positive Hermite--Biehler channel supplies a nonzero projective
  amplitude;
* the spectral separation is realized by the Cauchy carrier;
* the chiral quotient acts as a multiplier on that carrier;
* the completed `dslope` is the amplitude-weighted difference between the
  Cauchy Gram and the multiplier Gram.

This module keeps the two ambient channels separate.  It proves the exact
signed realization before asking for positivity.  Consequently the signed
form becomes positive semidefinite exactly when the already isolated chiral
multiplier is contractive; no Gram positivity is inserted into the carrier
definition.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

noncomputable section

/-! ## Ambient pair and projective twist -/

/-- Ambient carrier retaining separately the Cauchy source channel and its
chiral-multiplier image. -/
abbrev CanonicalCompletedNativeProjectiveChiralCarrier :=
  CanonicalCompletedNativeChiralCauchyCarrier ×
    CanonicalCompletedNativeChiralCauchyCarrier

/-- Linear projective/chiral graph transform.  It sends an ambient Cauchy
vector `u` to the positive-amplitude twist of `(u, q(z) u)`, where `q` is
the canonical completed Hermite--Biehler quotient. -/
def canonicalCompletedNativeProjectiveChiralTransform (z : ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier →ₗ[ℂ]
      CanonicalCompletedNativeProjectiveChiralCarrier where
  toFun u :=
    completedNativeNormalizedPositiveChiralAmplitude z •
      (u, completedNativeHermiteBiehlerChiralQuotient z • u)
  map_add' u v := by
    ext <;> simp [smul_add]
  map_smul' c u := by
    ext <;> simp [smul_smul, mul_comm, mul_left_comm]

/-- The unweighted source/multiplier pair on the canonical radial grid. -/
def canonicalCompletedNativeRadialChiralDefectState
    (k n : ℕ) : CanonicalCompletedNativeProjectiveChiralCarrier :=
  (completedNativeRadialChiralCauchyState k n,
    completedNativeRadialChiralMultiplierState k n)

/-- Projective transformation of the ambient pair by the exact positive
Hermite--Biehler amplitude. -/
def canonicalCompletedNativeRadialProjectiveChiralState
    (k n : ℕ) : CanonicalCompletedNativeProjectiveChiralCarrier :=
  completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k n) •
    canonicalCompletedNativeRadialChiralDefectState k n

/-- The radial state is literally the projective/chiral graph transform of
the canonical Cauchy feature. -/
theorem canonicalCompletedNativeRadialProjectiveChiralState_eq_transform
    (k n : ℕ) :
    canonicalCompletedNativeRadialProjectiveChiralState k n =
      canonicalCompletedNativeProjectiveChiralTransform
        (canonicalCompletedC3RadialTiltPoint k n)
        (completedNativeRadialChiralCauchyState k n) := by
  rfl

/-- Signed chiral form.  The factor `1/2` is forced by the normalized
positive chiral polarization and is not an adjustable normalization. -/
def canonicalCompletedNativeProjectiveChiralForm
    (u v : CanonicalCompletedNativeProjectiveChiralCarrier) : ℂ :=
  (2 : ℂ)⁻¹ * (inner ℂ u.1 v.1 - inner ℂ u.2 v.2)

/-- Finite matrix read out from the projectively twisted signed form. -/
def canonicalCompletedNativeRadialProjectiveChiralSampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedNativeProjectiveChiralForm
      (canonicalCompletedNativeRadialProjectiveChiralState k i)
      (canonicalCompletedNativeRadialProjectiveChiralState k j)

/-! ## Exact identification with the completed-native kernel -/

/-- Entrywise, the projective chiral form is exactly the completed-native
polarized `dslope`.  Both ambient channels remain explicit in the left-hand
side. -/
theorem canonicalCompletedNativeRadialProjectiveChiralForm_eq_dslope
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i j : Fin N) :
    canonicalCompletedNativeProjectiveChiralForm
        (canonicalCompletedNativeRadialProjectiveChiralState k i)
        (canonicalCompletedNativeRadialProjectiveChiralState k j) =
      canonicalCompletedNativeRadialDslopeSampleMatrix k N i j := by
  rw [canonicalCompletedNativeRadialDslopeSampleMatrix_eq_pickCongruence
    k N hregular]
  unfold canonicalCompletedNativeProjectiveChiralForm
    canonicalCompletedNativeRadialProjectiveChiralState
    canonicalCompletedNativeRadialChiralDefectState
  rw [canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect]
  simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left,
    inner_smul_right, Matrix.smul_apply, Matrix.mul_diagonal,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Pi.star_apply,
    starRingEnd_apply, canonicalCompletedNativeRadialChiralMultiplierDefectMatrix,
    Matrix.sub_apply, Matrix.gram_apply, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

/-- Matrix form of the exact projective/chiral identification. -/
theorem canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_eq_dslope
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    canonicalCompletedNativeRadialProjectiveChiralSampleMatrix k N =
      canonicalCompletedNativeRadialDslopeSampleMatrix k N := by
  ext i j
  exact canonicalCompletedNativeRadialProjectiveChiralForm_eq_dslope
    k N hregular i j

/-! ## Positivity audit -/

/-- The projective signed form is positive semidefinite on a finite radial
family exactly when the concrete chiral multiplier is contractive there.
This theorem isolates the sole step needed to turn the exact signed carrier
into a positive Hilbert carrier. -/
theorem
    canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_posSemidef_iff_contractive
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (canonicalCompletedNativeRadialProjectiveChiralSampleMatrix
        k N).PosSemidef ↔
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k N := by
  rw [canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_eq_dslope
      k N hregular,
    canonicalCompletedNativeRadialDslopeSampleMatrix_posSemidef_iff_pick
      k N hregular]
  exact
    (canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
      k N).symm

/-! ## Centered all-order germ -/

/-- The regularity needed by the exact projective formula is automatic
eventually on every finite section of the centered radial germ. -/
theorem canonicalCompletedNativeRadialProjectiveChiral_eventually_regular
    (N : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
  rw [Filter.eventually_all]
  intro i
  exact (canonicalCompletedC3RadialTiltPoint_tendsto_zero i).eventually
    completedNativeChiralPickFactorization_eventually_regular

/-- Every finite projective/chiral matrix eventually agrees exactly with the
corresponding completed-native `dslope` sample matrix. -/
theorem canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_eventually_eq_dslope
    (N : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      canonicalCompletedNativeRadialProjectiveChiralSampleMatrix k N =
        canonicalCompletedNativeRadialDslopeSampleMatrix k N := by
  filter_upwards [
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
      with k hregular
  exact canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_eq_dslope
    k N hregular

/-- Positivity of every finite projective/chiral germ matrix.  This
definition records the property but does not assume or prove it. -/
def CanonicalCompletedNativeRadialProjectiveChiralEventuallyPosSemidefinite :
    Prop :=
  ∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
    (canonicalCompletedNativeRadialProjectiveChiralSampleMatrix
      k N).PosSemidef

/-- The projective/chiral carrier has positive finite germs exactly when the
canonical chiral graph multiplier is eventually contractive. -/
theorem
    canonicalCompletedNativeRadialProjectiveChiralEventuallyPosSemidefinite_iff_contractive :
    CanonicalCompletedNativeRadialProjectiveChiralEventuallyPosSemidefinite ↔
      CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive := by
  constructor
  · intro hprojective N
    filter_upwards [hprojective N,
      canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
        with k hk hregular
    exact
      (canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_posSemidef_iff_contractive
        k N hregular).mp hk
  · intro hcontractive N
    filter_upwards [hcontractive N,
      canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
        with k hk hregular
    exact
      (canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_posSemidef_iff_contractive
        k N hregular).mpr hk

end

end CarrySelfAdjointOperator

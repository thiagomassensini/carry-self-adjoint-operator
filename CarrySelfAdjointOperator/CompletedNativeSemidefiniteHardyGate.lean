import CarrySelfAdjointOperator.AllPrefixPSDNonrecurrence
import CarrySelfAdjointOperator.CompletedNativeChiralBoundaryParityCoordinates
import CarrySelfAdjointOperator.CompletedNativeHardyAnalytic
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
import Mathlib.Tactic

/-!
# Conditional strict Hankel positivity from the original source boundary

The only sign premise here is nonnegativity of the original finite boundary
energies. The Hardy theorem supplies nonrecurrence; the parity split transports
the source sign to the two canonical moment towers.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators ComplexConjugate Matrix
open Filter Topology
open ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

private def sourceMomentCrossQuadratic {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, M i j * (conj (u i) * u j).re

private theorem sourceMomentCrossQuadratic_ofReal {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    sourceMomentCrossQuadratic M (fun i => (u i : ℂ)) =
      star u ⬝ᵥ (M *ᵥ u) := by
  simp only [sourceMomentCrossQuadratic, dotProduct, Matrix.mulVec,
    Pi.star_apply, star_trivial, Finset.mul_sum, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, mul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Nonnegative original source boundary energies imply semidefiniteness of
the unshifted canonical Hankel tower. The factor four is the one in the
original even/odd boundary split. -/
theorem canonicalHankel_posSemidef_of_nativeSourceBoundary_nonneg
    (hEnergy : ∀ n (x : Fin (2*n) → ℂ),
      0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∀ n, (hankelGram canonicalCompletedNativeLogDerivativeMoment n).PosSemidef := by
  intro n
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr
      (hankelGram_isSymm canonicalCompletedNativeLogDerivativeMoment n))
  intro u
  let y : Fin n → ℂ := fun i => (u i : ℂ)
  let x := nativeSourceBoundaryFromParity n y 0
  have hsource := hEnergy n x
  rw [nativeSourceFiniteBoundaryEnergy_even_split,
    nativeSourceEvenBoundaryPhase_fromParity,
    nativeSourceOddBoundaryPhase_fromParity] at hsource
  simp only [Pi.zero_apply, starRingEnd_apply, star_zero, mul_zero,
    Complex.zero_re, Finset.sum_const_zero, add_zero] at hsource
  change 0 ≤ 4 * sourceMomentCrossQuadratic
    (hankelGram primeDepthGeometricMoment n) y at hsource
  rw [primeDepthGeometricMoment_eq_canonical,
    sourceMomentCrossQuadratic_ofReal] at hsource
  have hq : 0 ≤ 4 * (star u ⬝ᵥ
      (hankelGram canonicalCompletedNativeLogDerivativeMoment n *ᵥ u)) := by
    simpa [y] using hsource
  linarith

/-- Nonnegative original source boundary energies imply semidefiniteness of
the one-step shifted canonical Hankel tower. -/
theorem canonicalShiftedHankel_posSemidef_of_nativeSourceBoundary_nonneg
    (hEnergy : ∀ n (x : Fin (2*n) → ℂ),
      0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∀ n, (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n).PosSemidef := by
  intro n
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr
      (shiftedHankel_isSymm canonicalCompletedNativeLogDerivativeMoment n))
  intro u
  let y : Fin n → ℂ := fun i => (u i : ℂ)
  let x := nativeSourceBoundaryFromParity n 0 y
  have hsource := hEnergy n x
  rw [nativeSourceFiniteBoundaryEnergy_even_split,
    nativeSourceEvenBoundaryPhase_fromParity,
    nativeSourceOddBoundaryPhase_fromParity] at hsource
  simp only [Pi.zero_apply, starRingEnd_apply, star_zero, mul_zero,
    Complex.zero_re, Finset.sum_const_zero, zero_add] at hsource
  change 0 ≤ 4 * sourceMomentCrossQuadratic
    (shiftedHankel primeDepthGeometricMoment n) y at hsource
  rw [primeDepthGeometricMoment_eq_canonical,
    sourceMomentCrossQuadratic_ofReal] at hsource
  have hq : 0 ≤ 4 * (star u ⬝ᵥ
      (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n *ᵥ u)) := by
    simpa [y] using hsource
  linarith

/-- Conditional all-order strict positivity: Hardy nonrecurrence excludes a
null vector in every PSD source-derived Hankel prefix. No source sign is
proved by this theorem; it remains the explicit `hEnergy` premise. -/
theorem canonicalHankelPair_posDef_of_nativeSourceBoundary_nonneg
    (hzeros : InfinitePositiveRealNativeZeros)
    (hEnergy : ∀ n (x : Fin (2*n) → ℂ),
      0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x) :
    (∀ n, (hankelGram canonicalCompletedNativeLogDerivativeMoment n).PosDef) ∧
    (∀ n, (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n).PosDef) := by
  have hno : NoFiniteMomentRelation canonicalCompletedNativeLogDerivativeMoment :=
    canonicalCompletedNativeLogDerivativeMoment_noFiniteMomentRelation_of_infinitePositiveRealNativeZeros
      hzeros
  have hno0 : NoFiniteMomentRelationAt canonicalCompletedNativeLogDerivativeMoment 0 := by
    simpa [NoFiniteMomentRelation, NoFiniteMomentRelationAt] using hno
  have hno1 : NoFiniteMomentRelationAt canonicalCompletedNativeLogDerivativeMoment 1 :=
    noFiniteMomentRelationAt_of_noFiniteMomentRelation hno 1
  have hpsd0 := canonicalHankel_posSemidef_of_nativeSourceBoundary_nonneg hEnergy
  have hpsd1 := canonicalShiftedHankel_posSemidef_of_nativeSourceBoundary_nonneg hEnergy
  constructor
  · intro n
    have hp := momentHankelPrefix_posDef_of_all_posSemidef_of_noFiniteMomentRelationAt
      canonicalCompletedNativeLogDerivativeMoment 0
      (fun N => by
        have h := hpsd0 N
        have heq : momentHankelPrefix canonicalCompletedNativeLogDerivativeMoment 0 N =
            hankelGram canonicalCompletedNativeLogDerivativeMoment N := by
          ext i j
          simp [momentHankelPrefix, hankelGram]
        rw [← heq] at h
        exact h)
      hno0
    have h := hp n
    have heq : momentHankelPrefix canonicalCompletedNativeLogDerivativeMoment 0 n =
        hankelGram canonicalCompletedNativeLogDerivativeMoment n := by
      ext i j
      simp [momentHankelPrefix, hankelGram]
    rw [← heq]
    exact h
  · intro n
    have hp := momentHankelPrefix_posDef_of_all_posSemidef_of_noFiniteMomentRelationAt
      canonicalCompletedNativeLogDerivativeMoment 1
      (fun N => by
        have h := hpsd1 N
        have heq : momentHankelPrefix canonicalCompletedNativeLogDerivativeMoment 1 N =
            shiftedHankel canonicalCompletedNativeLogDerivativeMoment N := by
          ext i j
          simp [momentHankelPrefix, shiftedHankel, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm]
        rw [← heq] at h
        exact h)
      hno1
    have h := hp n
    have heq : momentHankelPrefix canonicalCompletedNativeLogDerivativeMoment 1 n =
        shiftedHankel canonicalCompletedNativeLogDerivativeMoment n := by
      ext i j
      simp [momentHankelPrefix, shiftedHankel, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm]
    rw [← heq]
    exact h

/-- The exact signed Gamma correction gap in the original geometric chart.
It is `rawGammaBalance.im - ‖gammaSourceSynthesis‖²`; no scalar source or
completion factor is changed. -/
def nativeSourceGammaCorrectionGap (n k : ℕ) (x : Fin (2*n) → ℂ) : ℝ :=
  let c := nativeSourceChiralJetInput n k x
  (rawGammaWronskianBalance k c c 1 1).im - ‖gammaSourceSynthesis k c 1‖^2

/-- A conditional eventual envelope for the signed Gamma correction, at every
fixed order. This is an input proposition; this file does not claim it holds. -/
def HasNativeSourceGammaCorrectionEnvelope : Prop :=
  ∀ n, ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      nativeSourceGammaCorrectionGap n k x ≤ ε k * ‖x‖^2

/-- Any eventual signed correction envelope tending to zero forces
nonnegativity of the original boundary energy at each fixed order. The proof
uses the existing raw-Gamma-to-boundary error estimate with arbitrary positive
accuracy; neither the envelope nor its sign is proved here. -/
theorem nativeSourceFiniteBoundaryEnergy_nonneg_of_gammaCorrectionEnvelope
    (henv : HasNativeSourceGammaCorrectionEnvelope)
    (n : ℕ) (x : Fin (2*n) → ℂ) :
    0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x := by
  rcases henv n with ⟨ε, hε, hbound⟩
  by_cases hx : x = 0
  · subst x
    simp [nativeSourceFiniteBoundaryEnergy]
  · let E := nativeSourceFiniteBoundaryEnergy (2*n) x
    by_contra hE
    have hEneg : E < 0 := by simpa [E] using hE
    let R := ‖x‖^2
    have hR : 0 < R := by
      dsimp [R]
      exact pow_pos (norm_pos_iff.mpr hx) 2
    let δ := (-E) / (10*R)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact div_pos (neg_pos.mpr hEneg) (by positivity)
    have happ := rawGamma_chiralJetInput_eventually_energy_control n δ hδ
    have heps : ∀ᶠ k : ℕ in atTop, ε k < δ :=
      hε.eventually (Iio_mem_nhds hδ)
    have hElowerEventually : ∀ᶠ k : ℕ in atTop, E ≥ -5 * δ * R := by
      filter_upwards [happ, hbound, heps] with k happ hk hεk
      have happrox := happ x
      have hgap := hk x
      let c := nativeSourceChiralJetInput n k x
      have happroxLo :
          -4 * ((rawGammaWronskianBalance k c c 1 1).im -
            ‖gammaSourceSynthesis k c 1‖^2) - E ≤ δ * R := by
        have hupp := (abs_le.mp happrox).2
        dsimp [R, E] at hupp ⊢
        dsimp [c]
        nlinarith
      have hgapR : (rawGammaWronskianBalance k c c 1 1).im -
          ‖gammaSourceSynthesis k c 1‖^2 ≤ ε k * R := by
        simpa [nativeSourceGammaCorrectionGap, R, c] using hgap
      have hεR : ε k * R ≤ δ * R :=
        mul_le_mul_of_nonneg_right hεk.le hR.le
      nlinarith [happroxLo, hgapR, hεR]
    rcases hElowerEventually.exists with ⟨k, hElower⟩
    have hδR : δ * R = -E/10 := by
      dsimp [δ]
      field_simp [ne_of_gt hR]
    nlinarith [hElower, hδR]

/-- Conditional transport from a Gamma correction envelope to strict
positivity of both canonical Hankel towers. The envelope remains an explicit
open hypothesis, so this is not an unconditional all-order sign theorem. -/
theorem canonicalHankelPair_posDef_of_gammaCorrectionEnvelope
    (hzeros : InfinitePositiveRealNativeZeros)
    (henv : HasNativeSourceGammaCorrectionEnvelope) :
    (∀ n, (hankelGram canonicalCompletedNativeLogDerivativeMoment n).PosDef) ∧
    (∀ n, (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n).PosDef) := by
  apply canonicalHankelPair_posDef_of_nativeSourceBoundary_nonneg hzeros
  intro n x
  exact nativeSourceFiniteBoundaryEnergy_nonneg_of_gammaCorrectionEnvelope henv n x

end

end CarrySelfAdjointOperator

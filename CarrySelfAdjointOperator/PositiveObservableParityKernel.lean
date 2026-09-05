import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# A real positive-observable parity kernel

For a bounded symmetric real operator `S`, the two-channel state
`(r_t, t S r_t)` satisfies an exact polarized identity whenever
`r_t - t^2 S^2 r_t = u`.  The construction and its cyclic coefficient Grams
work in an arbitrary real inner product space, including infinite-dimensional
Hilbert spaces.  No native moment positivity or native readout identification
is assumed here.  Resolvent existence is kept separate from the algebraic
identity, so the theorem does not silently identify spectral and height domains.
-/

namespace CarrySelfAdjointOperator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Real version of the repository's `WithLp 2` binary Hilbert carrier. -/
abbrev PositiveObservableParityCarrier (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] := WithLp 2 (H × H)

/-- The parity state associated with a chosen resolvent vector. -/
def positiveObservableParityState (S : H →L[ℝ] H) (t : ℝ) (r : H) :
    PositiveObservableParityCarrier H :=
  WithLp.toLp 2 (r, t • S r)

/-- Both channels and their mixed parameter factor are retained in the Gram. -/
theorem inner_positiveObservableParityState
    (S : H →L[ℝ] H) (x z : ℝ) (rx rz : H) :
    inner ℝ (positiveObservableParityState S x rx)
      (positiveObservableParityState S z rz) =
        inner ℝ rx rz + x * z * inner ℝ (S rx) (S rz) := by
  rw [WithLp.prod_inner_apply]
  simp only [positiveObservableParityState, WithLp.ofLp_toLp,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Division-free polarized identity for the square observable `V = S^2`.
The equations are supplied only at the two parameters being compared. -/
theorem positiveObservableParityState_polarized
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u rx rz : H) (x z : ℝ)
    (hx : rx - x ^ 2 • S (S rx) = u)
    (hz : rz - z ^ 2 • S (S rz) = u) :
    (z - x) * inner ℝ (positiveObservableParityState S x rx)
        (positiveObservableParityState S z rz) =
      z * inner ℝ u rz - x * inner ℝ u rx := by
  have hxinner : inner ℝ u rz =
      inner ℝ rx rz - x ^ 2 * inner ℝ (S rx) (S rz) := by
    rw [← hx, inner_sub_left, real_inner_smul_left]
    exact congrArg (fun a : ℝ => inner ℝ rx rz - x ^ 2 * a)
      (hS (S rx) rz)
  have hzinner : inner ℝ u rx =
      inner ℝ rx rz - z ^ 2 * inner ℝ (S rx) (S rz) := by
    rw [← hz, inner_sub_left, real_inner_smul_left]
    rw [show inner ℝ (S (S rz)) rx = inner ℝ (S rz) (S rx) from hS (S rz) rx]
    rw [real_inner_comm rz rx, real_inner_comm (S rz) (S rx)]
  rw [inner_positiveObservableParityState, hxinner, hzinner]
  ring

/-- Off-diagonal divided-difference form, with the positive sign convention. -/
theorem positiveObservableParityState_inner_eq_dividedDifference
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u rx rz : H) (x z : ℝ) (hxz : z ≠ x)
    (hx : rx - x ^ 2 • S (S rx) = u)
    (hz : rz - z ^ 2 • S (S rz) = u) :
    inner ℝ (positiveObservableParityState S x rx)
        (positiveObservableParityState S z rz) =
      (z * inner ℝ u rz - x * inner ℝ u rx) / (z - x) := by
  apply (eq_div_iff (sub_ne_zero.mpr hxz)).2
  simpa [mul_comm] using
    positiveObservableParityState_polarized S hS u rx rz x z hx hz

/-- A definite resolvent vector, using the algebra inverse of `I - t^2 S^2`.
Only its valid resolvent domain is used in the theorems below. -/
def positiveObservableResolventVector
    (S : H →L[ℝ] H) (u : H) (t : ℝ) : H :=
  Ring.inverse (1 - t ^ 2 • (S * S)) u

/-- The explicit local bound on the square-root observable is a Neumann bound. -/
theorem positiveObservable_neumannBound
    (S : H →L[ℝ] H) (t : ℝ) (ht : |t| * ‖S‖ < 1) :
    ‖t ^ 2 • (S * S)‖ < 1 := by
  calc
    ‖t ^ 2 • (S * S)‖ = |t| ^ 2 * ‖S * S‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
    _ ≤ |t| ^ 2 * (‖S‖ * ‖S‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le S S) (sq_nonneg |t|)
    _ = (|t| * ‖S‖) ^ 2 := by ring
    _ < 1 := by
      have hnonneg := mul_nonneg (abs_nonneg t) (norm_nonneg S)
      nlinarith

/-- On the local Neumann domain, the concrete vector solves the resolvent equation. -/
theorem positiveObservableResolventVector_equation [CompleteSpace H]
    (S : H →L[ℝ] H) (u : H) (t : ℝ) (ht : |t| * ‖S‖ < 1) :
    positiveObservableResolventVector S u t -
        t ^ 2 • S (S (positiveObservableResolventVector S u t)) = u := by
  have hunit : IsUnit (1 - t ^ 2 • (S * S)) :=
    isUnit_one_sub_of_norm_lt_one (positiveObservable_neumannBound S t ht)
  have h := congrArg (fun T : H →L[ℝ] H => T u)
    (Ring.mul_inverse_cancel (1 - t ^ 2 • (S * S)) hunit)
  simpa [positiveObservableResolventVector, mul_apply_eq_comp] using h

/-- Concrete one-point state on the local resolvent domain. -/
def positiveObservableResolventParityState
    (S : H →L[ℝ] H) (u : H) (t : ℝ) : PositiveObservableParityCarrier H :=
  positiveObservableParityState S t (positiveObservableResolventVector S u t)

/-- The scalar response whose divided difference is the concrete parity Gram. -/
def positiveObservableResolventResponse
    (S : H →L[ℝ] H) (u : H) (t : ℝ) : ℝ :=
  t * inner ℝ u (positiveObservableResolventVector S u t)

/-- The actual local resolvent family satisfies the polarized kernel identity. -/
theorem positiveObservableResolventParityState_polarized [CompleteSpace H]
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u : H) (x z : ℝ) (hx : |x| * ‖S‖ < 1) (hz : |z| * ‖S‖ < 1) :
    (z - x) * inner ℝ (positiveObservableResolventParityState S u x)
        (positiveObservableResolventParityState S u z) =
      positiveObservableResolventResponse S u z -
        positiveObservableResolventResponse S u x :=
  positiveObservableParityState_polarized S hS u _ _ x z
    (positiveObservableResolventVector_equation S u x hx)
    (positiveObservableResolventVector_equation S u z hz)

/-- Every finite section is positive semidefinite before a readout is identified. -/
theorem positiveObservableParityState_gram_posSemidef
    (S : H →L[ℝ] H) {ι : Type*} [Fintype ι]
    (time : ι → ℝ) (state : ι → H) :
    (Matrix.of fun i j =>
      inner ℝ (positiveObservableParityState S (time i) (state i))
        (positiveObservableParityState S (time j) (state j))).PosSemidef := by
  exact Matrix.posSemidef_gram ℝ _

/-- Powers of the symmetric square-root observable on a fixed cyclic source. -/
def positiveObservableOrbit (S : H →L[ℝ] H) (u : H) (n : ℕ) : H :=
  (S.toLinearMap ^ n) u

/-- Moving a power through the inner product gives the full orbit Gram. -/
theorem inner_positiveObservableOrbit
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u : H) (i j : ℕ) :
    inner ℝ (positiveObservableOrbit S u i) (positiveObservableOrbit S u j) =
      inner ℝ u (positiveObservableOrbit S u (i + j)) := by
  unfold positiveObservableOrbit
  rw [hS.pow i u ((S.toLinearMap ^ j) u)]
  rw [← Module.End.mul_apply, ← pow_add]

/-- Moments of the positive observable `S^2` at the source `u`. -/
def positiveObservableMoment (S : H →L[ℝ] H) (u : H) (n : ℕ) : ℝ :=
  inner ℝ u (positiveObservableOrbit S u (2 * n))

/-- The moments are squared norms of the square-root orbit. -/
theorem positiveObservableMoment_eq_norm_sq
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u : H) (n : ℕ) :
    positiveObservableMoment S u n = ‖positiveObservableOrbit S u n‖ ^ 2 := by
  rw [positiveObservableMoment, show 2 * n = n + n by omega,
    ← inner_positiveObservableOrbit S hS u n n, real_inner_self_eq_norm_sq]

/-- The two coefficient families keep even and odd powers in orthogonal channels. -/
def positiveObservableParityJet (S : H →L[ℝ] H) (u : H) :
    ℕ ⊕ ℕ → PositiveObservableParityCarrier H
  | Sum.inl n => WithLp.toLp 2 (positiveObservableOrbit S u (2 * n), 0)
  | Sum.inr n => WithLp.toLp 2 (0, positiveObservableOrbit S u (2 * n + 1))

/-- The even Gram is the ordinary moment Hankel kernel. -/
theorem inner_positiveObservableParityJet_even
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u : H) (i j : ℕ) :
    inner ℝ (positiveObservableParityJet S u (Sum.inl i))
        (positiveObservableParityJet S u (Sum.inl j)) =
      positiveObservableMoment S u (i + j) := by
  simp only [positiveObservableParityJet, WithLp.prod_inner_apply,
    inner_zero_left, add_zero]
  rw [inner_positiveObservableOrbit S hS]
  congr 2
  omega

/-- The odd Gram is the shifted moment Hankel kernel. -/
theorem inner_positiveObservableParityJet_odd
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u : H) (i j : ℕ) :
    inner ℝ (positiveObservableParityJet S u (Sum.inr i))
        (positiveObservableParityJet S u (Sum.inr j)) =
      positiveObservableMoment S u (i + j + 1) := by
  simp only [positiveObservableParityJet, WithLp.prod_inner_apply,
    inner_zero_left, zero_add]
  rw [inner_positiveObservableOrbit S hS]
  congr 2
  omega

/-- The two parity channels are orthogonal. -/
@[simp] theorem inner_positiveObservableParityJet_even_odd
    (S : H →L[ℝ] H) (u : H) (i j : ℕ) :
    inner ℝ (positiveObservableParityJet S u (Sum.inl i))
      (positiveObservableParityJet S u (Sum.inr j)) = 0 := by
  simp [positiveObservableParityJet, WithLp.prod_inner_apply]

/-- Independence of the even cyclic powers survives the channel embedding. -/
theorem positiveObservableParityJet_even_linearIndependent
    (S : H →L[ℝ] H) (u : H)
    (hcyclic : LinearIndependent ℝ (fun n => positiveObservableOrbit S u (2 * n))) :
    LinearIndependent ℝ (fun n => positiveObservableParityJet S u (Sum.inl n)) := by
  apply LinearIndependent.of_comp (WithLp.fstL 2 ℝ H H).toLinearMap
  exact hcyclic

/-- Independence of the odd cyclic powers survives the channel embedding. -/
theorem positiveObservableParityJet_odd_linearIndependent
    (S : H →L[ℝ] H) (u : H)
    (hcyclic : LinearIndependent ℝ (fun n => positiveObservableOrbit S u (2 * n + 1))) :
    LinearIndependent ℝ (fun n => positiveObservableParityJet S u (Sum.inr n)) := by
  apply LinearIndependent.of_comp (WithLp.sndL 2 ℝ H H).toLinearMap
  exact hcyclic

/-- One explicit nondegenerate cyclic-orbit condition supplies both parity families. -/
theorem positiveObservableParityJet_linearIndependent_of_cyclic
    (S : H →L[ℝ] H) (u : H)
    (hcyclic : LinearIndependent ℝ (positiveObservableOrbit S u)) :
    LinearIndependent ℝ (fun n => positiveObservableParityJet S u (Sum.inl n)) ∧
      LinearIndependent ℝ (fun n => positiveObservableParityJet S u (Sum.inr n)) := by
  constructor
  · apply positiveObservableParityJet_even_linearIndependent S u
    exact hcyclic.comp (fun n => 2 * n) (by intro i j h; dsimp at h; omega)
  · apply positiveObservableParityJet_odd_linearIndependent S u
    exact hcyclic.comp (fun n => 2 * n + 1) (by intro i j h; dsimp at h; omega)

/-- Every ordinary Hankel section of the observable moments is positive semidefinite. -/
theorem positiveObservableMoment_hankel_posSemidef
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric) (u : H) (N : ℕ) :
    (Matrix.of fun i j : Fin N => positiveObservableMoment S u (i + j)).PosSemidef := by
  have h := Matrix.posSemidef_gram ℝ
    (fun i : Fin N => positiveObservableParityJet S u (Sum.inl i))
  simpa only [Matrix.gram, inner_positiveObservableParityJet_even S hS] using h

/-- Every shifted Hankel section of the observable moments is positive semidefinite. -/
theorem positiveObservableMoment_shiftedHankel_posSemidef
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric) (u : H) (N : ℕ) :
    (Matrix.of fun i j : Fin N => positiveObservableMoment S u (i + j + 1)).PosSemidef := by
  have h := Matrix.posSemidef_gram ℝ
    (fun i : Fin N => positiveObservableParityJet S u (Sum.inr i))
  simpa only [Matrix.gram, inner_positiveObservableParityJet_odd S hS] using h

/-- Nondegenerate cyclic powers give strict positivity in both channels, at every order. -/
theorem positiveObservableMoment_hankelPair_posDef_of_cyclic
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric) (u : H)
    (hcyclic : LinearIndependent ℝ (positiveObservableOrbit S u)) (N : ℕ) :
    (Matrix.of fun i j : Fin N => positiveObservableMoment S u (i + j)).PosDef ∧
      (Matrix.of fun i j : Fin N => positiveObservableMoment S u (i + j + 1)).PosDef := by
  obtain ⟨heven, hodd⟩ := positiveObservableParityJet_linearIndependent_of_cyclic S u hcyclic
  constructor
  · have h := Matrix.posDef_gram_of_linearIndependent
      (heven.comp (fun i : Fin N => (i : ℕ)) Fin.val_injective)
    simpa only [Matrix.gram, Function.comp_apply,
      inner_positiveObservableParityJet_even S hS] using h
  · have h := Matrix.posDef_gram_of_linearIndependent
      (hodd.comp (fun i : Fin N => (i : ℕ)) Fin.val_injective)
    simpa only [Matrix.gram, Function.comp_apply,
      inner_positiveObservableParityJet_odd S hS] using h

end

end CarrySelfAdjointOperator

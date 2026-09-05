import CarrySelfAdjointOperator.PositiveObservableParityKernel
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The actual Neumann series of the positive-observable kernel

The orbit powers used by the moment bridge are the convergent coefficient
series of the constructed resolvent vector and its parity state.  This also
identifies the scalar response with the generating series of those same
moments.  The statements use the explicit local domain `|t| * ‖S‖ < 1` and
hold on an arbitrary complete real inner product space.  No native moment
identity or cyclic independence is assumed for this analytic connection.
-/

namespace CarrySelfAdjointOperator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Evaluation of a Neumann operator power gives exactly an even orbit term. -/
theorem positiveObservable_neumannPower_apply
    (S : H →L[ℝ] H) (u : H) (t : ℝ) (n : ℕ) :
    ((t ^ 2 • (S * S)) ^ n) u =
      t ^ (2 * n) • positiveObservableOrbit S u (2 * n) := by
  rw [smul_pow, ← pow_mul, ← pow_two, ← pow_mul]
  simp only [smul_apply]
  congr 1
  change (S ^ (2 * n)).toLinearMap u = (S.toLinearMap ^ (2 * n)) u
  rw [ContinuousLinearMap.coe_pow]

/-- The actual resolvent vector is the sum of its even orbit series. -/
theorem positiveObservableResolventVector_hasSum
    (S : H →L[ℝ] H) (u : H) (t : ℝ) (ht : |t| * ‖S‖ < 1) :
    HasSum (fun n : ℕ => t ^ (2 * n) • positiveObservableOrbit S u (2 * n))
      (positiveObservableResolventVector S u t) := by
  have hgeom := hasSum_geom_series_inverse (t ^ 2 • (S * S))
    (positiveObservable_neumannBound S t ht)
  have heval := (ContinuousLinearMap.apply ℝ H u).hasSum hgeom
  simpa only [ContinuousLinearMap.apply_apply, positiveObservable_neumannPower_apply,
    positiveObservableResolventVector] using heval

/-- The resolvent vector as an explicit vector-valued sum. -/
theorem positiveObservableResolventVector_eq_tsum
    (S : H →L[ℝ] H) (u : H) (t : ℝ) (ht : |t| * ‖S‖ < 1) :
    positiveObservableResolventVector S u t =
      ∑' n : ℕ, t ^ (2 * n) • positiveObservableOrbit S u (2 * n) :=
  (positiveObservableResolventVector_hasSum S u t ht).tsum_eq.symm

omit [CompleteSpace H] in
/-- Applying the square-root observable advances its cyclic orbit by one. -/
theorem positiveObservableOrbit_succ
    (S : H →L[ℝ] H) (u : H) (n : ℕ) :
    S (positiveObservableOrbit S u n) = positiveObservableOrbit S u (n + 1) := by
  simp only [positiveObservableOrbit, pow_succ', Module.End.mul_apply,
    ContinuousLinearMap.coe_coe]

/-- The second state channel is the sum of the odd orbit series. -/
theorem positiveObservableResolventOddChannel_hasSum
    (S : H →L[ℝ] H) (u : H) (t : ℝ) (ht : |t| * ‖S‖ < 1) :
    HasSum (fun n : ℕ =>
      t ^ (2 * n + 1) • positiveObservableOrbit S u (2 * n + 1))
      (t • S (positiveObservableResolventVector S u t)) := by
  have h := (S.hasSum (positiveObservableResolventVector_hasSum S u t ht)).const_smul t
  simpa only [map_smul, positiveObservableOrbit_succ, smul_smul,
    pow_succ, mul_comm t] using h

/-- Pairing with the source gives the convergent generating series of the moments. -/
theorem positiveObservableResolventResponse_hasSum
    (S : H →L[ℝ] H) (u : H) (t : ℝ) (ht : |t| * ‖S‖ < 1) :
    HasSum (fun n : ℕ => t ^ (2 * n + 1) * positiveObservableMoment S u n)
      (positiveObservableResolventResponse S u t) := by
  have h := ((innerSL ℝ u).hasSum
    (positiveObservableResolventVector_hasSum S u t ht)).mul_left t
  change HasSum (fun n : ℕ =>
      t * inner ℝ u (t ^ (2 * n) • positiveObservableOrbit S u (2 * n)))
    (positiveObservableResolventResponse S u t) at h
  convert h using 1
  ext n
  rw [real_inner_smul_right]
  simp only [positiveObservableMoment, pow_succ]
  ring

/-- The scalar kernel readout is the sum of the same moments used by its Gram. -/
theorem positiveObservableResolventResponse_eq_tsum
    (S : H →L[ℝ] H) (u : H) (t : ℝ) (ht : |t| * ‖S‖ < 1) :
    positiveObservableResolventResponse S u t =
      ∑' n : ℕ, t ^ (2 * n + 1) * positiveObservableMoment S u n :=
  (positiveObservableResolventResponse_hasSum S u t ht).tsum_eq.symm

/-- The two-channel state is exactly the convergent paired parity-jet series. -/
theorem positiveObservableResolventParityState_hasSum
    (S : H →L[ℝ] H) (u : H) (t : ℝ) (ht : |t| * ‖S‖ < 1) :
    HasSum (fun n : ℕ =>
      t ^ (2 * n) • positiveObservableParityJet S u (Sum.inl n) +
        t ^ (2 * n + 1) • positiveObservableParityJet S u (Sum.inr n))
      (positiveObservableResolventParityState S u t) := by
  have hp := (positiveObservableResolventVector_hasSum S u t ht).prodMk
    (positiveObservableResolventOddChannel_hasSum S u t ht)
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ H H).symm.toContinuousLinearMap.hasSum hp
  change HasSum (fun n : ℕ => WithLp.toLp 2
      (t ^ (2 * n) • positiveObservableOrbit S u (2 * n),
        t ^ (2 * n + 1) • positiveObservableOrbit S u (2 * n + 1)))
    (WithLp.toLp 2 (positiveObservableResolventVector S u t,
      t • S (positiveObservableResolventVector S u t))) at h
  simpa only [positiveObservableResolventParityState, positiveObservableParityState,
    positiveObservableParityJet, ← WithLp.toLp_smul, ← WithLp.toLp_add,
    Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add] using h

/-- Explicit sum form of the parity state. -/
theorem positiveObservableResolventParityState_eq_tsum
    (S : H →L[ℝ] H) (u : H) (t : ℝ) (ht : |t| * ‖S‖ < 1) :
    positiveObservableResolventParityState S u t =
      ∑' n : ℕ,
        (t ^ (2 * n) • positiveObservableParityJet S u (Sum.inl n) +
          t ^ (2 * n + 1) • positiveObservableParityJet S u (Sum.inr n)) :=
  (positiveObservableResolventParityState_hasSum S u t ht).tsum_eq.symm

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.RelationalLogGapCommutator

namespace CarrySelfAdjointOperator.LogGapConnection
open CPFormal.Analytic.Cp FiniteClockJets MaterialCameraJets
open scoped BigOperators
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- Finite integral of the oriented edges, with no infinite nodal state. -/
def edgePrefix {N : ℕ} (d : FiniteRealSpectralHilbert N) (j : ℕ) : ℂ :=
  ∑ q : Fin N, if q.val < j then d q else 0

theorem edgePrefix_succ {N : ℕ} (d : FiniteRealSpectralHilbert N) (j : Fin N) :
    edgePrefix d (j.val+1) = edgePrefix d j.val + d j := by
  have he : ∀ q : Fin N,
      (if q.val < j.val+1 then d q else 0) =
        (if q.val < j.val then d q else 0) + (if q = j then d q else 0) := by
    intro q
    by_cases hlt : q.val < j.val
    · have hne : q ≠ j := by intro h; subst q; omega
      simp [hlt, hne, show q.val < j.val+1 by omega]
    · by_cases heq : q = j
      · subst q; simp
      · have hv : q.val ≠ j.val := by intro h; exact heq (Fin.ext h)
        simp [hlt, heq, show ¬ q.val < j.val+1 by omega]
  simp only [edgePrefix, he, Finset.sum_add_distrib]
  simp

theorem material_sample_reconstruction {N : ℕ} (x : FiniteRealSpectralHilbert (N+1))
    (j : Fin (N+1)) : x j = x 0 + edgePrefix (finiteMaterialGradient N x) j.val := by
  induction j using Fin.induction with
  | zero => simp [edgePrefix]
  | succ j ih =>
    simp only [Fin.val_succ] at *
    rw [edgePrefix_succ]
    change x j.succ = x 0 + (edgePrefix (finiteMaterialGradient N x) j.val +
      (x j.succ - x j.castSucc))
    change x j.castSucc = x 0 + edgePrefix (finiteMaterialGradient N x) j.val at ih
    linear_combination ih

/-- Explicit finite seed + gradient equivalence; no unitarity assertion. -/
def materialSeedGradientEquiv (N : ℕ) :
    FiniteRealSpectralHilbert (N+1) ≃ₗ[ℂ] ℂ × FiniteRealSpectralHilbert N where
  toFun x := (x 0, finiteMaterialGradient N x)
  invFun y := WithLp.toLp 2 (fun j => y.1 + edgePrefix y.2 j.val)
  left_inv x := by
    ext j
    exact (material_sample_reconstruction x j).symm
  right_inv y := by
    apply Prod.ext
    · simp [edgePrefix]
    · ext j
      change (y.1 + edgePrefix y.2 (j.val+1)) -
        (y.1 + edgePrefix y.2 j.val) = y.2 j
      rw [edgePrefix_succ]
      ring
  map_add' x y := by simp [map_add]
  map_smul' c x := by simp [map_smul]

/-- Discrete all-order product rule on every physical finite state. -/
theorem materialGradient_jet_productRule {N : ℕ} (r : ℕ)
    (x : FiniteRealSpectralHilbert (N+1)) (q : Fin N) :
    finiteMaterialGradient N (materialJet r x) q =
      positiveLogVertexWeight q.val^r * finiteMaterialGradient N x q +
        logEdgePowerWeight q.val r * x q.succ := by
  rw [logEdgePowerWeight_eq_difference]
  change materialJet r x q.succ - materialJet r x q.castSucc =
    positiveLogVertexWeight q.val^r * (x q.succ - x q.castSucc) +
      (positiveLogVertexWeight (q.val+1)^r-positiveLogVertexWeight q.val^r)*x q.succ
  simp only [materialJet_apply, finiteRealSpectralFrequency, positiveLogVertexWeight,
    Fin.val_succ, Fin.val_castSucc, Nat.add_assoc]
  ring

private theorem edgePrefix_add {N : ℕ} (d e : FiniteRealSpectralHilbert N) (j : ℕ) :
    edgePrefix (d+e) j = edgePrefix d j + edgePrefix e j := by
  change (∑ q : Fin N, if q.val < j then d q+e q else 0) = _
  have h (q : Fin N) : (if q.val < j then d q+e q else 0) =
      (if q.val < j then d q else 0) + (if q.val < j then e q else 0) := by
    split_ifs <;> simp
  simp_rw [h]
  exact Finset.sum_add_distrib

private theorem edgePrefix_smul {N : ℕ} (c : ℂ) (d : FiniteRealSpectralHilbert N) (j : ℕ) :
    edgePrefix (c • d) j = c * edgePrefix d j := by
  change (∑ q : Fin N, if q.val < j then c*d q else 0) = _
  have h (q : Fin N) : (if q.val < j then c*d q else 0) =
      c * (if q.val < j then d q else 0) := by split_ifs <;> simp
  simp_rw [h]
  exact (Finset.mul_sum _ _ _).symm

/-- Explicit operator on the existing product carrier, derived from the
Leibniz rule and finite reconstruction, NOT defined by conjugation. -/
def seededMaterialJet (N r : ℕ) : Module.End ℂ (ℂ × FiniteRealSpectralHilbert N) where
  toFun y := (positiveLogVertexWeight 0^r * y.1,
    WithLp.toLp 2 (fun q => positiveLogVertexWeight q.val^r * y.2 q +
      logEdgePowerWeight q.val r * (y.1 + edgePrefix y.2 (q.val+1))))
  map_add' y z := by
    apply Prod.ext
    · simp [mul_add]
    · ext q
      change positiveLogVertexWeight q.val^r * (y.2 q+z.2 q) +
        logEdgePowerWeight q.val r * (y.1+z.1+edgePrefix (y.2+z.2) (q.val+1)) =
          (positiveLogVertexWeight q.val^r*y.2 q +
            logEdgePowerWeight q.val r*(y.1+edgePrefix y.2 (q.val+1))) +
          (positiveLogVertexWeight q.val^r*z.2 q +
            logEdgePowerWeight q.val r*(z.1+edgePrefix z.2 (q.val+1)))
      rw [edgePrefix_add]
      ring
  map_smul' c y := by
    apply Prod.ext
    · simp; ring
    · ext q
      change positiveLogVertexWeight q.val^r * (c*y.2 q) +
        logEdgePowerWeight q.val r * (c*y.1+edgePrefix (c • y.2) (q.val+1)) =
          c*(positiveLogVertexWeight q.val^r*y.2 q +
            logEdgePowerWeight q.val r*(y.1+edgePrefix y.2 (q.val+1)))
      rw [edgePrefix_smul]
      ring

/-- The diagram commutes as a vector identity, preserving seed and all edges. -/
theorem seededMaterialJet_intertwines (N r : ℕ)
    (x : FiniteRealSpectralHilbert (N+1)) :
    materialSeedGradientEquiv N (materialJet r x) =
      seededMaterialJet N r (materialSeedGradientEquiv N x) := by
  apply Prod.ext
  · change materialJet r x 0 = positiveLogVertexWeight 0^r * x 0
    rw [materialJet_apply]
    rfl
  · ext q
    change finiteMaterialGradient N (materialJet r x) q =
      positiveLogVertexWeight q.val^r * finiteMaterialGradient N x q +
        logEdgePowerWeight q.val r * (x 0 + edgePrefix (finiteMaterialGradient N x) (q.val+1))
    rw [materialGradient_jet_productRule]
    have h := material_sample_reconstruction x q.succ
    simp only [Fin.val_succ] at h
    rw [← h]

theorem seededMaterialJet_zero (N : ℕ) : seededMaterialJet N 0 = 1 := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (materialSeedGradientEquiv N).surjective y
  rw [← seededMaterialJet_intertwines]
  simp [materialJet]

theorem seededMaterialJet_add_order (N r s : ℕ) :
    seededMaterialJet N r * seededMaterialJet N s = seededMaterialJet N (r+s) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (materialSeedGradientEquiv N).surjective y
  change seededMaterialJet N r (seededMaterialJet N s (materialSeedGradientEquiv N x)) = _
  rw [← seededMaterialJet_intertwines, ← seededMaterialJet_intertwines,
    ← seededMaterialJet_intertwines, materialJet_add_order]

theorem seededMaterialJet_eq_clock_power (N r : ℕ) :
    seededMaterialJet N r = seededMaterialJet N 1 ^ r := by
  induction r with
  | zero => simp [seededMaterialJet_zero]
  | succ r ih => rw [← seededMaterialJet_add_order, ih, pow_succ]

/-- Seed of L is zero because the actual first material frequency is log(1). -/
theorem seededMaterialClock_seed (N : ℕ) (y : ℂ × FiniteRealSpectralHilbert N) :
    (seededMaterialJet N 1 y).1 = 0 := by
  simp [seededMaterialJet, positiveLogVertexWeight]

/-- Both product-rule orientations apply to arbitrary samples, not only Dirichlet. -/
theorem materialGradient_clock_right_productRule {N : ℕ}
    (x : FiniteRealSpectralHilbert (N+1)) (q : Fin N) :
    finiteMaterialGradient N (materialJet 1 x) q =
      positiveLogVertexWeight (q.val+1) * finiteMaterialGradient N x q +
        positiveLogGap q.val * x q.castSucc := by
  rw [materialGradient_jet_productRule, logEdgePowerWeight_eq_difference]
  have hg : positiveLogGap q.val = positiveLogVertexWeight (q.val+1)-positiveLogVertexWeight q.val := by
    simp [positiveLogGap, positiveLogVertexWeight, Nat.add_assoc]
  rw [hg]
  simp only [pow_one]
  change positiveLogVertexWeight q.val * (x q.succ-x q.castSucc) +
    (positiveLogVertexWeight (q.val+1)-positiveLogVertexWeight q.val)*x q.succ =
      positiveLogVertexWeight (q.val+1)*(x q.succ-x q.castSucc) +
        (positiveLogVertexWeight (q.val+1)-positiveLogVertexWeight q.val)*x q.castSucc
  ring

theorem finiteDirichletSamples_gradient (N : ℕ) (s : ℂ) (q : Fin N) :
    finiteMaterialGradient N (finiteDirichletSamples (N+1) s) q = positiveDirichletGradient s q.val := by
  rw [positiveDirichletGradient_eq_value_sub_value]
  simp [finiteMaterialGradient, finiteDirichletSamples, realDirichletPower,
    positiveDirichletValue, Nat.add_assoc]
  congr 1
  ring

theorem finiteDirichletSamples_clockGradient (N : ℕ) (s : ℂ) (q : Fin N) :
    finiteMaterialGradient N (materialJet 1 (finiteDirichletSamples (N+1) s)) q =
      positiveLogDirichletGradient s q.val := by
  rw [materialGradient_clock_right_productRule, finiteDirichletSamples_gradient,
    canonicalC3LogGradient_right_productRule]
  simp [finiteDirichletSamples, realDirichletPower, positiveDirichletValue]

/-- Exact typed comparison of TWO independent sources and adjacent edges.
The ordinary and clock-gradient vectors precede the existing mixed readout. -/
theorem finiteDirichletSamples_mixedAdjacentClock (N : ℕ) (z w : ℂ) (q : Fin N) :
    sameSEdgeBoundaryWedge
      (finiteMaterialGradient (N+1) (finiteDirichletSamples (N+2) w) q.castSucc)
      (finiteMaterialGradient (N+1) (finiteDirichletSamples (N+2) w) q.succ)
      (finiteMaterialGradient (N+1) (materialJet 1 (finiteDirichletSamples (N+2) z)) q.castSucc)
      (finiteMaterialGradient (N+1) (materialJet 1 (finiteDirichletSamples (N+2) z)) q.succ) =
      (canonicalC3AdjacentClockChannels z w q.val).1 +
        (canonicalC3AdjacentClockChannels z w q.val).2 := by
  rw [finiteDirichletSamples_gradient, finiteDirichletSamples_gradient,
    finiteDirichletSamples_clockGradient, finiteDirichletSamples_clockGradient]
  exact canonicalC3AdjacentClockChannels_eq_mixedWedge z w q.val

/-- The raw critical Taylor seed remains a separate finite coordinate.
Only order zero has seed one; all positive clock orders have seed zero. -/
theorem criticalMaterialTaylor_seed (N r : ℕ) :
    ((-Complex.I)^r / (r.factorial : ℂ)) *
      materialJet r (finiteDirichletSamples (N+1) (1/2)) 0 =
        if r = 0 then (1 : ℂ) else 0 := by
  by_cases hr : r = 0
  · subst r
    simp [materialJet_apply, finiteRealSpectralFrequency, finiteDirichletSamples, realDirichletPower]
  · simp [materialJet_apply, finiteRealSpectralFrequency, hr]

/-- Seed + slopes have a product limit, without an infinite nodal reconstruction. -/
theorem criticalSeededTfvdTaylor_tendsto (r : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((-Complex.I)^r / (r.factorial : ℂ)) *
          materialJet r (finiteDirichletSamples (N+1) (1/2)) 0,
         materialTfvdTaylorPrefix N r))
      Filter.atTop (nhds (if r = 0 then (1 : ℂ) else 0,
        canonicalCompletedNativeTfvdTaylorCoefficientState r)) := by
  simp_rw [criticalMaterialTaylor_seed]
  exact tendsto_const_nhds.prodMk_nhds (materialTfvdTaylorPrefix_tendsto r)

/-- The same finite seed is retained together with BOTH ordinary/log TFVD channels. -/
theorem criticalSeededTfvdEnrichedTaylor_tendsto (r : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((-Complex.I)^r / (r.factorial : ℂ)) *
          materialJet r (finiteDirichletSamples (N+1) (1/2)) 0,
         materialTfvdEnrichedTaylorPrefix N r))
      Filter.atTop (nhds (if r = 0 then (1 : ℂ) else 0,
        canonicalCompletedNativeTfvdEnrichedTaylorRawJet r)) := by
  simp_rw [criticalMaterialTaylor_seed]
  exact tendsto_const_nhds.prodMk_nhds (materialTfvdEnrichedTaylorPrefix_tendsto r)

end
end CarrySelfAdjointOperator.LogGapConnection

import CarrySelfAdjointOperator.CompletedNativeTfvdCoefficientJets
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Strict causal Gram from native TFVD coefficients

The finite logarithmic coefficient family is transported through the actual
weighted bracket Green response while the boundary return remains a separate
Hilbert coordinate.  Exact TFVD reconstruction makes the channel-complete
transport injective.  The resulting finite Gram is therefore positive
definite without using a moment kernel, a zero condition, or spectral input.
-/

open scoped BigOperators ComplexOrder lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The first `N` coordinates of the first `N` odd logarithmic slope jets. -/
def nativeOddLogPowerSlopeJetFinite (N : ℕ) (order : Fin N) : Fin N → ℂ :=
  fun coordinate => nativeOddLogPowerSlopeJet order.val coordinate.val

/-- Restricting to the first `N` coordinates already detects every linear
combination of the first `N` odd logarithmic slope jets. -/
theorem nativeOddLogPowerSlopeJetFinite_linearIndependent (N : ℕ) :
    LinearIndependent ℂ (nativeOddLogPowerSlopeJetFinite N) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum i
  let frequency : Fin N → ℂ := fun j =>
    ((Real.log ((j.val + 2 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)
  have hcoordinate (n : Fin N) :
      ∑ r : Fin N,
          coeff r * nativeOddLogPowerSlopeJet r.val n.val = 0 := by
    have h := congrArg (fun state : Fin N → ℂ => state n) hsum
    simpa only [nativeOddLogPowerSlopeJetFinite, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have hcumulative (j : Fin N) :
      ∑ r : Fin N,
          coeff r *
            (nativeCriticalDirichletAmplitude (j.val + 2) *
              (Real.log ((j.val + 2 : ℕ) : ℝ) : ℂ) ^
                (2 * r.val + 1)) = 0 := by
    calc
      _ = ∑ n ∈ Finset.range (j.val + 1),
          ∑ r : Fin N, coeff r * nativeOddLogPowerSlopeJet r.val n := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro r hr
            rw [← Finset.mul_sum, sum_nativeOddLogPowerSlopeJet]
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro n hn
            exact hcoordinate
              ⟨n, by
                have hn' := Finset.mem_range.mp hn
                omega⟩
  have hvandermonde (j : Fin N) :
      ∑ r : Fin N, coeff r * frequency j ^ r.val = 0 := by
    let amplitude := nativeCriticalDirichletAmplitude (j.val + 2)
    let logFrequency : ℂ := (Real.log ((j.val + 2 : ℕ) : ℝ) : ℂ)
    have hamp : amplitude ≠ 0 := by
      unfold amplitude nativeCriticalDirichletAmplitude natDirichletTerm
        dirichletTerm
      simpa [show (j.val + 2 : ℕ) = (j.val + 1) + 1 by omega] using
        Complex.natCast_add_one_cpow_ne_zero (j.val + 1) (-(1 / 2 : ℂ))
    have hlog : logFrequency ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      exact (Real.log_pos (by
        exact_mod_cast (show 1 < j.val + 2 by omega))).ne'
    have hfactor :
        amplitude * logFrequency *
            (∑ r : Fin N, coeff r * frequency j ^ r.val) =
          ∑ r : Fin N,
            coeff r *
              (nativeCriticalDirichletAmplitude (j.val + 2) *
                (Real.log ((j.val + 2 : ℕ) : ℝ) : ℂ) ^
                  (2 * r.val + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      dsimp only [frequency, amplitude, logFrequency]
      push_cast
      rw [← pow_mul, pow_add]
      ring
    have hzero : amplitude * logFrequency *
        (∑ r : Fin N, coeff r * frequency j ^ r.val) = 0 := by
      rw [hfactor]
      exact hcumulative j
    exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hamp hlog)
  have hcoeff : coeff = 0 :=
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (nativePositiveLogSquaredFrequency_injective N) hvandermonde
  exact congrFun hcoeff i

/-- Hilbert carrier which keeps the causal response and the boundary return in
two distinct coordinates. -/
abbrev FiniteWeightedSlopeGreenBoundaryCarrier :=
  WithLp 2 (CarryVerticalL2 × CarryVerticalL2)

/-- Channel-separated causal transport of a finite slope coefficient vector. -/
def finiteWeightedSlopeGreenBoundaryLinearMap
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (Fin N → ℂ) →ₗ[ℂ] FiniteWeightedSlopeGreenBoundaryCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ CarryVerticalL2 CarryVerticalL2).symm.toLinearMap.comp
    ((finiteWeightedSlopeGreenResponseLinearMap q N).prod
      (finiteWeightedSlopeBoundaryReturnLinearMap q hq0 hq1 N))

@[simp] theorem finiteWeightedSlopeGreenBoundaryLinearMap_fst
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    (coeff : Fin N → ℂ) :
    (finiteWeightedSlopeGreenBoundaryLinearMap q hq0 hq1 N coeff).fst =
      finiteWeightedSlopeGreenResponseLinearMap q N coeff := by
  rfl

@[simp] theorem finiteWeightedSlopeGreenBoundaryLinearMap_snd
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    (coeff : Fin N → ℂ) :
    (finiteWeightedSlopeGreenBoundaryLinearMap q hq0 hq1 N coeff).snd =
      finiteWeightedSlopeBoundaryReturnLinearMap q hq0 hq1 N coeff := by
  rfl

/-- Adding the two retained channels recovers the original finite TFVD slope
state exactly. -/
theorem finiteWeightedSlopeGreenBoundaryLinearMap_sum
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (N : ℕ)
    (coeff : Fin N → ℂ) :
    (finiteWeightedSlopeGreenBoundaryLinearMap q hqpos.le hq1 N coeff).fst +
        (finiteWeightedSlopeGreenBoundaryLinearMap q hqpos.le hq1 N coeff).snd =
      finiteSlopeCoefficientSynthesisLinearMap N coeff := by
  rw [finiteWeightedSlopeGreenBoundaryLinearMap_fst,
    finiteWeightedSlopeGreenBoundaryLinearMap_snd]
  exact finiteWeightedSlopeGreenResponse_add_boundaryReturn
    q hqpos hq1 N coeff

/-- Exact reconstruction makes the separated response/boundary transport
injective.  No positivity argument is used. -/
theorem finiteWeightedSlopeGreenBoundaryLinearMap_injective
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (N : ℕ) :
    Function.Injective
      (finiteWeightedSlopeGreenBoundaryLinearMap q hqpos.le hq1 N) := by
  intro a b hab
  have hsum := congrArg
    (fun state : FiniteWeightedSlopeGreenBoundaryCarrier =>
      state.fst + state.snd) hab
  rw [finiteWeightedSlopeGreenBoundaryLinearMap_sum q hqpos hq1 N a,
    finiteWeightedSlopeGreenBoundaryLinearMap_sum q hqpos hq1 N b] at hsum
  exact finiteSlopeCoefficientSynthesisLinearMap_injective N hsum

/-- The native odd-log coefficient family after the actual causal Green and
boundary transport. -/
def canonicalFiniteNativeCausalGreenBoundaryJet
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (N : ℕ) (order : Fin N) : FiniteWeightedSlopeGreenBoundaryCarrier :=
  finiteWeightedSlopeGreenBoundaryLinearMap
    (canonicalBR2CarryAmplitudeRatio base)
    (canonicalBR2CarryAmplitudeRatio_pos hbase).le
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase) N
    (nativeOddLogPowerSlopeJetFinite N order)

/-- The complete native causal Green/boundary jets are linearly independent at
every finite order. -/
theorem canonicalFiniteNativeCausalGreenBoundaryJet_linearIndependent
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (N : ℕ) :
    LinearIndependent ℂ
      (canonicalFiniteNativeCausalGreenBoundaryJet hbase N) := by
  let transport := finiteWeightedSlopeGreenBoundaryLinearMap
    (canonicalBR2CarryAmplitudeRatio base)
    (canonicalBR2CarryAmplitudeRatio_pos hbase).le
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase) N
  have hmapped := (nativeOddLogPowerSlopeJetFinite_linearIndependent N).map_injOn
    transport
    (finiteWeightedSlopeGreenBoundaryLinearMap_injective
      (canonicalBR2CarryAmplitudeRatio base)
      (canonicalBR2CarryAmplitudeRatio_pos hbase)
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) N).injOn
  change LinearIndependent ℂ (fun order : Fin N =>
    finiteWeightedSlopeGreenBoundaryLinearMap
      (canonicalBR2CarryAmplitudeRatio base)
      (canonicalBR2CarryAmplitudeRatio_pos hbase).le
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) N
      (nativeOddLogPowerSlopeJetFinite N order))
  exact hmapped

/-- The finite native TFVD state obtained after the final response-plus-boundary
readout. -/
def canonicalFiniteNativeTfvdSlopeJet
    (N : ℕ) (order : Fin N) : CarryVerticalL2 :=
  finiteSlopeCoefficientSynthesisLinearMap N
    (nativeOddLogPowerSlopeJetFinite N order)

/-- The separated causal carrier reconstructs the native TFVD jet exactly;
in particular, no boundary or mixed term is discarded. -/
theorem canonicalFiniteNativeCausalGreenBoundaryJet_sum
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (N : ℕ) (order : Fin N) :
    (canonicalFiniteNativeCausalGreenBoundaryJet hbase N order).fst +
        (canonicalFiniteNativeCausalGreenBoundaryJet hbase N order).snd =
      canonicalFiniteNativeTfvdSlopeJet N order := by
  exact finiteWeightedSlopeGreenBoundaryLinearMap_sum
    (canonicalBR2CarryAmplitudeRatio base)
    (canonicalBR2CarryAmplitudeRatio_pos hbase)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase) N
    (nativeOddLogPowerSlopeJetFinite N order)

/-- Exact TFVD synthesis preserves the finite logarithmic Vandermonde
family. -/
theorem canonicalFiniteNativeTfvdSlopeJet_linearIndependent (N : ℕ) :
    LinearIndependent ℂ (canonicalFiniteNativeTfvdSlopeJet N) := by
  have hmapped := (nativeOddLogPowerSlopeJetFinite_linearIndependent N).map_injOn
    (finiteSlopeCoefficientSynthesisLinearMap N)
    (finiteSlopeCoefficientSynthesisLinearMap_injective N).injOn
  change LinearIndependent ℂ (fun order : Fin N =>
    finiteSlopeCoefficientSynthesisLinearMap N
      (nativeOddLogPowerSlopeJetFinite N order))
  exact hmapped

/-- The reconstructed native TFVD Gram, including the response/boundary cross
terms, is strictly positive at every finite order. -/
theorem canonicalFiniteNativeTfvdSlopeGram_posDef (N : ℕ) :
    (Matrix.gram ℂ (canonicalFiniteNativeTfvdSlopeJet N)).PosDef :=
  Matrix.posDef_gram_of_linearIndependent
    (canonicalFiniteNativeTfvdSlopeJet_linearIndependent N)

/-- The separated causal Gram is strictly positive at every finite order,
derived only from the carry source transform, causal reconstruction, boundary
return, and the native logarithmic Vandermonde family. -/
theorem canonicalFiniteNativeCausalGreenBoundaryGram_posDef
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (N : ℕ) :
    (Matrix.gram ℂ
      (canonicalFiniteNativeCausalGreenBoundaryJet hbase N)).PosDef :=
  Matrix.posDef_gram_of_linearIndependent
    (canonicalFiniteNativeCausalGreenBoundaryJet_linearIndependent hbase N)

end

end CarrySelfAdjointOperator

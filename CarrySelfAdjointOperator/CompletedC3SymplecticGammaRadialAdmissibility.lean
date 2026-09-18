import CarrySelfAdjointOperator.CompletedC3SymplecticGammaRadialSamples
import CarrySelfAdjointOperator.CompletedC3SymplecticGammaExplicitCompletedLedger
import Mathlib.Tactic

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter Topology

noncomputable section

theorem
canonicalCompletedC3RadialTiltPoint_eventually_mem_genuineCriticalStrip
    (n : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      operatorHeightParameter
          (canonicalCompletedC3RadialTiltPoint k n) ∈
        CPFormal.Analytic.Cp.genuineCriticalStrip := by
  filter_upwards [canonicalCompletedC3RadialTiltPoint_eventually_admissible n] with
    k hk
  exact hk.1

theorem
canonicalCompletedC3RadialTiltPair_eventually_mem_genuineCriticalStrip
    (i j : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      operatorHeightParameter
          (canonicalCompletedC3RadialTiltPoint steps.1 i) ∈
        CPFormal.Analytic.Cp.genuineCriticalStrip ∧
      operatorHeightParameter
          (canonicalCompletedC3RadialTiltPoint steps.2 j) ∈
        CPFormal.Analytic.Cp.genuineCriticalStrip := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  filter_upwards [
    hfst.eventually
      (canonicalCompletedC3RadialTiltPoint_eventually_mem_genuineCriticalStrip i),
    hsnd.eventually
      (canonicalCompletedC3RadialTiltPoint_eventually_mem_genuineCriticalStrip j)
  ] with steps hi hj
  exact ⟨hi, hj⟩

theorem
canonicalCompletedC3RadialTiltStencil_eventually_mem_genuineCriticalStrip
    (p q : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      ∀ i ∈ Finset.range (p + 1),
        ∀ j ∈ Finset.range (q + 1),
          operatorHeightParameter
              (canonicalCompletedC3RadialTiltPoint steps.1 i) ∈
            CPFormal.Analytic.Cp.genuineCriticalStrip ∧
          operatorHeightParameter
              (canonicalCompletedC3RadialTiltPoint steps.2 j) ∈
            CPFormal.Analytic.Cp.genuineCriticalStrip := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hi : ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (p + 1),
        operatorHeightParameter
            (canonicalCompletedC3RadialTiltPoint k i) ∈
          CPFormal.Analytic.Cp.genuineCriticalStrip :=
    (Finset.range (p + 1)).eventually_all.2 fun i hi =>
      canonicalCompletedC3RadialTiltPoint_eventually_mem_genuineCriticalStrip i
  have hj : ∀ᶠ k : ℕ in atTop,
      ∀ j ∈ Finset.range (q + 1),
        operatorHeightParameter
            (canonicalCompletedC3RadialTiltPoint k j) ∈
          CPFormal.Analytic.Cp.genuineCriticalStrip :=
    (Finset.range (q + 1)).eventually_all.2 fun j hj =>
      canonicalCompletedC3RadialTiltPoint_eventually_mem_genuineCriticalStrip j
  filter_upwards [hfst.eventually hi, hsnd.eventually hj] with steps hiSteps hjSteps
  intro i hii j hjj
  exact ⟨hiSteps i hii, hjSteps j hjj⟩

end

end CarrySelfAdjointOperator

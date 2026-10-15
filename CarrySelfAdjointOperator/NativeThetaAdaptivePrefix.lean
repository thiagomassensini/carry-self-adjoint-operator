import CarrySelfAdjointOperator.NativeThetaModeScore

/-! Finite score averages of the unchanged source. The integration weight is
always the FULL kernel. Prefix convergence does not assert pivot positivity. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
open Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeThetaPrefixWeight (K : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range K, nativeThetaModeWeight j u

def nativeThetaPrefixNumerator (K : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range K, nativeThetaModeScore j u*nativeThetaModeWeight j u

/-- K is the number of positive theta modes, not the largest zero-based index. -/
def nativeThetaPrefixScore (K : ℕ) (u : ℝ) : ℝ :=
  nativeThetaPrefixNumerator K u/nativeThetaPrefixWeight K u

theorem nativeThetaPrefixWeight_pos {K : ℕ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) :
    0 < nativeThetaPrefixWeight K u := by
  have h := Finset.single_le_sum (s := Finset.range K)
    (fun j _ => (nativeThetaModeWeight_pos j hu).le) (Finset.mem_range.mpr hK)
  exact (nativeThetaModeWeight_pos 0 hu).trans_le h

theorem nativeThetaModeParameter_mono {i j : ℕ} (hij : i ≤ j) (u : ℝ) :
    nativeThetaModeParameter i u ≤ nativeThetaModeParameter j u := by
  have hcast : ((i+1 : ℕ) : ℝ) ≤ ((j+1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hij 1
  have hsq : ((i+1 : ℕ) : ℝ)^2 ≤ ((j+1 : ℕ) : ℝ)^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (i+1)]
  unfold nativeThetaModeParameter
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq Real.pi_pos.le) (Real.exp_pos _).le

theorem nativeThetaModeScore_mono {i j : ℕ} (hij : i ≤ j) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaModeScore i u ≤ nativeThetaModeScore j u := by
  have hi := nativeThetaModeParameter_first_le i hu
  exact mul_le_mul_of_nonneg_left
    (nativeThetaModeSlope_mono (hi.1.trans hi.2) (nativeThetaModeParameter_mono hij u)) hu

theorem nativeThetaPrefixScore_first_le {K : ℕ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaModeScore 0 u ≤ nativeThetaPrefixScore K u := by
  apply (le_div_iff₀ (nativeThetaPrefixWeight_pos hK hu)).2
  simp only [nativeThetaPrefixWeight, nativeThetaPrefixNumerator, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (nativeThetaModeScore_first_le j hu)
    (nativeThetaModeWeight_pos j hu).le

theorem nativeThetaPrefixScore_le_tailMode {K j : ℕ} (hK : 0 < K) (hj : K ≤ j)
    {u : ℝ} (hu : 0 ≤ u) : nativeThetaPrefixScore K u ≤ nativeThetaModeScore j u := by
  apply (div_le_iff₀ (nativeThetaPrefixWeight_pos hK hu)).2
  simp only [nativeThetaPrefixNumerator, nativeThetaPrefixWeight, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (nativeThetaModeScore_mono (by have := Finset.mem_range.mp hi; omega) hu)
    (nativeThetaModeWeight_pos i hu).le

theorem nativeThetaModeScore_density_summable {u : ℝ} (hu : 0 ≤ u) :
    Summable (fun j => nativeThetaModeScore j u*nativeThetaModeWeight j u) := by
  apply ((nativeThetaModeFirst_summable u).mul_left (-u)).congr
  intro j
  exact (nativeThetaModeScore_mul_weight j hu).symm

theorem nativeThetaModeScore_density_tsum {u : ℝ} (hu : 0 ≤ u) :
    ∑' j : ℕ, nativeThetaModeScore j u*nativeThetaModeWeight j u =
      -u*completedNativeXiCosineKernelFirst u := by
  simp only [nativeThetaModeScore_mul_weight _ hu, tsum_mul_left, nativeThetaModeFirst_tsum]

/-- All omitted modes, with their original positive weights. -/
def nativeThetaPrefixRemainderDensity (K : ℕ) (u : ℝ) : ℝ :=
  ∑' j : ℕ, (nativeThetaModeScore (j+K) u-nativeThetaPrefixScore K u)*
    nativeThetaModeWeight (j+K) u

theorem nativeThetaPrefixRemainderDensity_nonneg {K : ℕ} (hK : 0 < K)
    {u : ℝ} (hu : 0 ≤ u) : 0 ≤ nativeThetaPrefixRemainderDensity K u := by
  apply tsum_nonneg
  intro j
  exact mul_nonneg (sub_nonneg.mpr (nativeThetaPrefixScore_le_tailMode hK (by omega) hu))
    (nativeThetaModeWeight_pos (j+K) hu).le

theorem nativeThetaPrefixRemainderDensity_eq {K : ℕ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaPrefixRemainderDensity K u =
      (nativeThetaScore u-nativeThetaPrefixScore K u)*completedNativeXiCosineKernel u := by
  let f := fun j => (nativeThetaModeScore j u-nativeThetaPrefixScore K u)*nativeThetaModeWeight j u
  have hs : Summable f := by
    have h := (nativeThetaModeScore_density_summable hu).sub
      ((nativeThetaModeWeight_summable u).mul_left (nativeThetaPrefixScore K u))
    apply h.congr
    intro j
    dsimp [f]
    ring
  have hhead : ∑ j ∈ Finset.range K, f j = 0 := by
    simp only [f, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change nativeThetaPrefixNumerator K u - nativeThetaPrefixScore K u*nativeThetaPrefixWeight K u = 0
    unfold nativeThetaPrefixScore
    field_simp [(nativeThetaPrefixWeight_pos hK hu).ne']
    ring
  have hsplit := hs.sum_add_tsum_nat_add K
  rw [hhead, zero_add] at hsplit
  change nativeThetaPrefixRemainderDensity K u = _ at hsplit
  rw [hsplit]
  have he : f = fun j => nativeThetaModeScore j u*nativeThetaModeWeight j u -
      nativeThetaPrefixScore K u*nativeThetaModeWeight j u := by funext j; dsimp [f]; ring
  rw [he, (nativeThetaModeScore_density_summable hu).tsum_sub
    ((nativeThetaModeWeight_summable u).mul_left (nativeThetaPrefixScore K u)),
    tsum_mul_left, nativeThetaModeScore_density_tsum hu, nativeThetaModeWeight_tsum]
  unfold nativeThetaScore
  field_simp [(completedNativeXiCosineKernel_pos hu).ne']

theorem nativeThetaPrefixScore_le_full {K : ℕ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaPrefixScore K u ≤ nativeThetaScore u := by
  have h := nativeThetaPrefixRemainderDensity_nonneg hK hu
  rw [nativeThetaPrefixRemainderDensity_eq hK hu] at h
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (completedNativeXiCosineKernel_pos hu)).mp h)

/-- Adding the next mode yields a nonnegative pointwise increment; the
signed polynomial used in the energy has not been applied yet. -/
theorem nativeThetaPrefixScore_increment {K : ℕ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaPrefixWeight (K+1) u*(nativeThetaPrefixScore (K+1) u-nativeThetaPrefixScore K u) =
      nativeThetaModeWeight K u*(nativeThetaModeScore K u-nativeThetaPrefixScore K u) := by
  have hw : nativeThetaPrefixWeight (K+1) u = nativeThetaPrefixWeight K u+nativeThetaModeWeight K u := by
    exact Finset.sum_range_succ _ _
  have hn : nativeThetaPrefixNumerator (K+1) u = nativeThetaPrefixNumerator K u+
      nativeThetaModeScore K u*nativeThetaModeWeight K u := by exact Finset.sum_range_succ _ _
  have hp := (nativeThetaPrefixWeight_pos hK hu).ne'
  have hpnext := (nativeThetaPrefixWeight_pos (by omega : 0 < K+1) hu).ne'
  unfold nativeThetaPrefixScore
  field_simp [hp,hpnext]
  rw [hw,hn]
  ring

theorem nativeThetaPrefixScore_mono_step {K : ℕ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaPrefixScore K u ≤ nativeThetaPrefixScore (K+1) u := by
  have h := mul_nonneg (nativeThetaModeWeight_pos K hu).le
    (sub_nonneg.mpr (nativeThetaPrefixScore_le_tailMode hK (le_refl K) hu))
  rw [← nativeThetaPrefixScore_increment hK hu] at h
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (nativeThetaPrefixWeight_pos (by omega) hu)).mp h)

/-- Pointwise convergence uses the actual infinite source series. -/
theorem nativeThetaPrefixScore_tendsto {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun K => nativeThetaPrefixScore K u) atTop (nhds (nativeThetaScore u)) := by
  have hn := (nativeThetaModeScore_density_summable hu).hasSum.tendsto_sum_nat
  have hd := (nativeThetaModeWeight_summable u).hasSum.tendsto_sum_nat
  rw [nativeThetaModeScore_density_tsum hu] at hn
  rw [nativeThetaModeWeight_tsum] at hd
  exact hn.div hd (completedNativeXiCosineKernel_pos hu).ne'

/-- A priori modal count used below: no matrix inverse, pivot or target sign
is consulted in choosing this count. -/
def nativeThetaAdaptiveModeCount (n : ℕ) : ℕ := n+2

theorem nativeThetaAdaptiveModeCount_pos (n : ℕ) : 0 < nativeThetaAdaptiveModeCount n := by
  unfold nativeThetaAdaptiveModeCount
  omega

end
end CarrySelfAdjointOperator

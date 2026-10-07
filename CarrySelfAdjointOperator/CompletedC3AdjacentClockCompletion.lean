import CarrySelfAdjointOperator.CompletedC3AdjacentClockGreenTransport

/-!
# Absolute completion of the two adjacent material-clock channels

The existing ordinary/logJet l1/l2 states bound the actual mixed product.
Literal log gaps and Dirichlet values bound its geometric endpoint return.
Thus both independently defined channels converge absolutely, without
assuming their signs or cancellation. The existing radial Green limit is
then transported. No raw nodal Hilbert state or new positive metric is used.
-/
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

/-- A uniform analytic bound for the literal positive log step. -/
theorem canonicalC3PositiveLogGap_norm_le_one (n : ℕ) : ‖positiveLogGap n‖ ≤ 1 := by
  let a : ℝ := (n + 1 : ℕ)
  let b : ℝ := (n + 2 : ℕ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := by dsimp [a, b]; norm_cast; omega
  have hba : b ≤ 2 * a := by dsimp [a, b]; push_cast; nlinarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hlog
  have hratio : b / a ≤ 2 := (div_le_iff₀ ha).2 (by simpa [mul_comm] using hba)
  have hnonneg : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha hab)
  change ‖((Real.log b : ℂ) - (Real.log a : ℂ))‖ ≤ 1
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  linarith

/-- Decay is used only as a pointwise bound, not as raw nodal l2 membership. -/
theorem canonicalC3PositiveValue_norm_le_one {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖positiveDirichletValue z n‖ ≤ 1 := by
  rw [norm_positiveDirichletValue]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by
    have h : 1 ≤ n + 1 := by omega
    exact_mod_cast h) (by linarith)

/-- Each log-gap return is dominated by the existing ordinary l1 sequence. -/
theorem canonicalC3AdjacentClockReturn_norm_le {z : ℂ} (hz : 0 < z.re) (w : ℂ) (n : ℕ) :
    ‖(canonicalC3AdjacentClockChannels z w n).2‖ ≤
      ‖positiveDirichletGradient w (n + 1)‖ + ‖positiveDirichletGradient w n‖ := by
  have hterm (i j l : ℕ) :
      ‖positiveLogGap i * positiveDirichletGradient w j * positiveDirichletValue z l‖ ≤
        ‖positiveDirichletGradient w j‖ := by
    rw [norm_mul, norm_mul]
    calc
      ‖positiveLogGap i‖ * ‖positiveDirichletGradient w j‖ * ‖positiveDirichletValue z l‖ ≤
          1 * ‖positiveDirichletGradient w j‖ * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (canonicalC3PositiveLogGap_norm_le_one i)
          (norm_nonneg _)) (canonicalC3PositiveValue_norm_le_one hz l)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact (norm_sub_le _ _).trans (add_le_add (hterm n (n+1) n) (hterm (n+1) n (n+2)))

/-- Existing bundled logJet coordinates supply a uniform bound for both clocks. -/
theorem canonicalC3AdjacentMixedWedge_norm_le {z : ℂ} (hz : 0 < z.re) (w : ℂ) (n : ℕ) :
    ‖sameSEdgeBoundaryWedge (positiveDirichletGradient w n) (positiveDirichletGradient w (n+1))
      (positiveLogDirichletGradient z n) (positiveLogDirichletGradient z (n+1))‖ ≤
    ‖canonicalCompletedC3LogJetState z hz‖ *
      (‖positiveDirichletGradient w (n+1)‖ + ‖positiveDirichletGradient w n‖) := by
  have hc (i : ℕ) : ‖positiveLogDirichletGradient z i‖ ≤ ‖canonicalCompletedC3LogJetState z hz‖ :=
    lp.norm_apply_le_norm (by norm_num) (canonicalCompletedC3LogJetState z hz) i
  unfold sameSEdgeBoundaryWedge
  calc
    ‖positiveDirichletGradient w (n+1) * positiveLogDirichletGradient z n -
        positiveDirichletGradient w n * positiveLogDirichletGradient z (n+1)‖ ≤
      ‖positiveDirichletGradient w (n+1) * positiveLogDirichletGradient z n‖ +
        ‖positiveDirichletGradient w n * positiveLogDirichletGradient z (n+1)‖ := norm_sub_le _ _
    _ ≤ ‖positiveDirichletGradient w (n+1)‖ * ‖canonicalCompletedC3LogJetState z hz‖ +
        ‖positiveDirichletGradient w n‖ * ‖canonicalCompletedC3LogJetState z hz‖ := by
      simpa only [norm_mul] using add_le_add
        (mul_le_mul_of_nonneg_left (hc n) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hc (n+1)) (norm_nonneg _))
    _ = _ := by ring

/-- Absolute summability of the geometric endpoint return. -/
theorem summable_norm_canonicalC3AdjacentClockReturn {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Summable (fun n => ‖(canonicalC3AdjacentClockChannels z w n).2‖) := by
  have hg := summable_norm_positiveDirichletGradient hw
  have hs := hg.comp_injective (show Function.Injective (fun n : ℕ => n+1) by intro a b h; dsimp only at h; omega)
  exact (hs.add hg).of_nonneg_of_le (fun _ => norm_nonneg _) (canonicalC3AdjacentClockReturn_norm_le hz w)

/-- Absolute summability of the independent material-frequency channel.
Its estimate uses the exact local transport, not a definition by subtraction. -/
theorem summable_norm_canonicalC3AdjacentOrdinaryClock {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Summable (fun n => ‖(canonicalC3AdjacentClockChannels z w n).1‖) := by
  have hg := summable_norm_positiveDirichletGradient hw
  have hs := hg.comp_injective (show Function.Injective (fun n : ℕ => n+1) by intro a b h; dsimp only at h; omega)
  have hm := (hs.add hg).mul_left (‖canonicalCompletedC3LogJetState z hz‖ + 1)
  apply hm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  have heq : (canonicalC3AdjacentClockChannels z w n).1 =
      sameSEdgeBoundaryWedge (positiveDirichletGradient w n) (positiveDirichletGradient w (n+1))
        (positiveLogDirichletGradient z n) (positiveLogDirichletGradient z (n+1)) -
        (canonicalC3AdjacentClockChannels z w n).2 := by
    exact eq_sub_of_add_eq (canonicalC3AdjacentClockChannels_eq_mixedWedge z w n).symm
  rw [heq]
  exact (norm_sub_le _ _).trans (by
    have h := add_le_add (canonicalC3AdjacentMixedWedge_norm_le hz w n)
      (canonicalC3AdjacentClockReturn_norm_le hz w n)
    convert h using 1
    simp only [Function.comp_def]
    ring)

/-- Whole C3 cells, keeping both clock channels separate before summation. -/
def canonicalC3AdjacentClockBlockChannels (z w : ℂ) (m : ℕ) : ℂ × ℂ :=
  ((canonicalC3AdjacentClockChannels z w (3*m)).1 + (canonicalC3AdjacentClockChannels z w (3*m+1)).1,
   (canonicalC3AdjacentClockChannels z w (3*m)).2 + (canonicalC3AdjacentClockChannels z w (3*m+1)).2)

/-- Both block projections are absolutely summable; no cancellation is used. -/
theorem canonicalC3AdjacentClockBlockChannels_summable_norm {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    Summable (fun m => ‖(canonicalC3AdjacentClockBlockChannels z w m).1‖) ∧
      Summable (fun m => ‖(canonicalC3AdjacentClockBlockChannels z w m).2‖) := by
  have inj0 : Function.Injective (fun m : ℕ => 3*m) := by intro a b h; dsimp only at h; omega
  have inj1 : Function.Injective (fun m : ℕ => 3*m+1) := by intro a b h; dsimp only at h; omega
  constructor
  · have h := summable_norm_canonicalC3AdjacentOrdinaryClock hz hw
    exact ((h.comp_injective inj0).add (h.comp_injective inj1)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun m => norm_add_le _ _)
  · have h := summable_norm_canonicalC3AdjacentClockReturn hz hw
    exact ((h.comp_injective inj0).add (h.comp_injective inj1)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun m => norm_add_le _ _)

/-- Completed source observations, defined from absolute sums of the two
independent geometric channels. This pair is not a new positive kernel. -/
def canonicalC3CompletedAdjacentClockChannels (z w : ℂ) : ℂ × ℂ :=
  (∑' m, (canonicalC3AdjacentClockBlockChannels z w m).1,
   ∑' m, (canonicalC3AdjacentClockBlockChannels z w m).2)

/-- Finite mixed-leg addressing is exactly whole-cell partial summation. -/
theorem canonicalC3AdjacentClockFiniteSum_eq_blocks (M : ℕ) (z w : ℂ) :
    ((∑ mr, (canonicalC3AdjacentClockChannelFamily M z w mr).1),
      (∑ mr, (canonicalC3AdjacentClockChannelFamily M z w mr).2)) =
      (∑ m ∈ Finset.range M, (canonicalC3AdjacentClockBlockChannels z w m).1,
       ∑ m ∈ Finset.range M, (canonicalC3AdjacentClockBlockChannels z w m).2) := by
  apply Prod.ext <;>
    simp only [canonicalC3AdjacentClockChannelFamily, canonicalC3AdjacentMaterialLegIndex,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.add_zero,
      canonicalC3AdjacentClockBlockChannels]
  · exact Fin.sum_univ_eq_sum_range (fun m =>
      (canonicalC3AdjacentClockChannels z w (3*m)).1 +
        (canonicalC3AdjacentClockChannels z w (3*m+1)).1) M
  · exact Fin.sum_univ_eq_sum_range (fun m =>
      (canonicalC3AdjacentClockChannels z w (3*m)).2 +
        (canonicalC3AdjacentClockChannels z w (3*m+1)).2) M

/-- Completion is componentwise, before the two scalar channels are added. -/
theorem canonicalC3AdjacentClockChannels_tendsto_completed {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    Tendsto (fun M => ((∑ mr, (canonicalC3AdjacentClockChannelFamily M z w mr).1),
      (∑ mr, (canonicalC3AdjacentClockChannelFamily M z w mr).2))) atTop
      (nhds (canonicalC3CompletedAdjacentClockChannels z w)) := by
  have h := canonicalC3AdjacentClockBlockChannels_summable_norm hz hw
  exact ((h.1.of_norm.tendsto_sum_tsum_nat).prodMk_nhds
    (h.2.of_norm.tendsto_sum_tsum_nat)).congr' (Eventually.of_forall fun M =>
      (canonicalC3AdjacentClockFiniteSum_eq_blocks M z w).symm)

/-- The completed current Green provenance contains both absolute clock
limits and the unchanged completed radial Green kernel. -/
theorem canonicalC3MixedGreenProvenance_tendsto_clockCompletion {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) (hRef : 0 < (reflectedParameter z).re) :
    Tendsto (fun M =>
      (canonicalC3AllCutoffMixedSourcePrefixState M z w).greenProvenanceReadout
        M w (reflectedParameter z)) atTop
      (nhds ((canonicalC3CompletedAdjacentClockChannels z w).1 +
        (canonicalC3CompletedAdjacentClockChannels z w).2 -
          canonicalCompletedC3MixedRadialGreenKernel z w hw hRef)) := by
  have h := canonicalC3AdjacentClockChannels_tendsto_completed hz hw
  have hA := (continuous_fst.tendsto _).comp h
  have hJ := (continuous_snd.tendsto _).comp h
  have hG := finiteC3MixedRadialGreen_tendsto_completed hw hRef
  refine ((hA.add hJ).sub hG).congr' (Eventually.of_forall fun M => ?_)
  dsimp only [Function.comp_def]
  rw [canonicalC3MixedPrefixGreenProvenance_clockTransport]
  simp only [canonicalC3AllCutoffMixedSourcePrefixState_wSource,
    canonicalC3AllCutoffMixedSourcePrefixState_reflectedZSource,
    canonicalC3AllCutoffGreenPort_prefix_eq]

end
end CarrySelfAdjointOperator

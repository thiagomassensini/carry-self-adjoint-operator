import CarrySelfAdjointOperator.tmp.ThetaTenthMomentCertificateData.ThetaCells000

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

theorem thetaTenth_first_integral_eq_sum_cells (p : ℕ) :
    (∫ x in (0:ℝ)..1, x^p*thetaFirstMode x) =
      ∑ j ∈ Finset.range 4, ∫ x in ((j:ℝ)/4)..
        (((j+1:ℕ):ℝ)/4), x^p*thetaFirstMode x := by
  have hint : ∀ k : ℕ, k < 4 →
      IntervalIntegrable (fun x : ℝ ↦ x^p*thetaFirstMode x)
        volume ((k:ℝ)/4) (((k+1:ℕ):ℝ)/4) := by
    intro k _
    apply Continuous.intervalIntegrable
    unfold thetaFirstMode
    fun_prop
  simpa using (intervalIntegral.sum_integral_adjacent_intervals hint).symm

theorem thetaTenth_second_integral_eq_sum_cells (p : ℕ) :
    (∫ x in (0:ℝ)..1, x^p*thetaSecondMode x) =
      ∑ j ∈ Finset.range 4, ∫ x in ((j:ℝ)/4)..
        (((j+1:ℕ):ℝ)/4), x^p*thetaSecondMode x := by
  have hint : ∀ k : ℕ, k < 4 →
      IntervalIntegrable (fun x : ℝ ↦ x^p*thetaSecondMode x)
        volume ((k:ℝ)/4) (((k+1:ℕ):ℝ)/4) := by
    intro k _
    apply Continuous.intervalIntegrable
    unfold thetaSecondMode
    fun_prop
  simpa using (intervalIntegral.sum_integral_adjacent_intervals hint).symm

theorem thetaTenth_first_integral_lower_0 :
    (40861377/4000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^0*thetaFirstMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_lower_0_000 thetaTenth_first_cell_lower_0_001) (add_le_add thetaTenth_first_cell_lower_0_002 thetaTenth_first_cell_lower_0_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_upper_0 :
    (∫ x in (0:ℝ)..1, x^0*thetaFirstMode x) ≤ (1129560323/80000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_upper_0_000 thetaTenth_first_cell_upper_0_001) (add_le_add thetaTenth_first_cell_upper_0_002 thetaTenth_first_cell_upper_0_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_lower_2 :
    (129018411/640000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^2*thetaFirstMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_lower_2_000 thetaTenth_first_cell_lower_2_001) (add_le_add thetaTenth_first_cell_lower_2_002 thetaTenth_first_cell_lower_2_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_upper_2 :
    (∫ x in (0:ℝ)..1, x^2*thetaFirstMode x) ≤ (2904175871/7680000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_upper_2_000 thetaTenth_first_cell_upper_2_001) (add_le_add thetaTenth_first_cell_upper_2_002 thetaTenth_first_cell_upper_2_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_lower_4 :
    (742809737/51200000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^4*thetaFirstMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_lower_4_000 thetaTenth_first_cell_lower_4_001) (add_le_add thetaTenth_first_cell_lower_4_002 thetaTenth_first_cell_lower_4_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_upper_4 :
    (∫ x in (0:ℝ)..1, x^4*thetaFirstMode x) ≤ (11858695031/307200000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_upper_4_000 thetaTenth_first_cell_upper_4_001) (add_le_add thetaTenth_first_cell_upper_4_002 thetaTenth_first_cell_upper_4_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_lower_6 :
    (310512487/163840000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^6*thetaFirstMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_lower_6_000 thetaTenth_first_cell_lower_6_001) (add_le_add thetaTenth_first_cell_lower_6_002 thetaTenth_first_cell_lower_6_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_upper_6 :
    (∫ x in (0:ℝ)..1, x^6*thetaFirstMode x) ≤ (64831871039/9175040000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_upper_6_000 thetaTenth_first_cell_upper_6_001) (add_le_add thetaTenth_first_cell_upper_6_002 thetaTenth_first_cell_upper_6_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_lower_8 :
    (8327485643/23592960000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^8*thetaFirstMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_lower_8_000 thetaTenth_first_cell_lower_8_001) (add_le_add thetaTenth_first_cell_lower_8_002 thetaTenth_first_cell_lower_8_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_upper_8 :
    (∫ x in (0:ℝ)..1, x^8*thetaFirstMode x) ≤ (438330339719/235929600000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_upper_8_000 thetaTenth_first_cell_upper_8_001) (add_le_add thetaTenth_first_cell_upper_8_002 thetaTenth_first_cell_upper_8_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_lower_10 :
    (38874954207/461373440000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^10*thetaFirstMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_lower_10_000 thetaTenth_first_cell_lower_10_001) (add_le_add thetaTenth_first_cell_lower_10_002 thetaTenth_first_cell_lower_10_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_first_integral_upper_10 :
    (∫ x in (0:ℝ)..1, x^10*thetaFirstMode x) ≤ (318376523917/503316480000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_first_cell_upper_10_000 thetaTenth_first_cell_upper_10_001) (add_le_add thetaTenth_first_cell_upper_10_002 thetaTenth_first_cell_upper_10_003))
  rw [thetaTenth_first_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_lower_0 :
    (523/10000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^0*thetaSecondMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_lower_0_000 thetaTenth_second_cell_lower_0_001) (add_le_add thetaTenth_second_cell_lower_0_002 thetaTenth_second_cell_lower_0_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_upper_0 :
    (∫ x in (0:ℝ)..1, x^0*thetaSecondMode x) ≤ (34899/40000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_upper_0_000 thetaTenth_second_cell_upper_0_001) (add_le_add thetaTenth_second_cell_upper_0_002 thetaTenth_second_cell_upper_0_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_lower_2 :
    (251/1920000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^2*thetaSecondMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_lower_2_000 thetaTenth_second_cell_lower_2_001) (add_le_add thetaTenth_second_cell_lower_2_002 thetaTenth_second_cell_lower_2_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_upper_2 :
    (∫ x in (0:ℝ)..1, x^2*thetaSecondMode x) ≤ (7031/768000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_upper_2_000 thetaTenth_second_cell_upper_2_001) (add_le_add thetaTenth_second_cell_upper_2_002 thetaTenth_second_cell_upper_2_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_lower_4 :
    (29/12800000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^4*thetaSecondMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_lower_4_000 thetaTenth_second_cell_lower_4_001) (add_le_add thetaTenth_second_cell_lower_4_002 thetaTenth_second_cell_lower_4_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_upper_4 :
    (∫ x in (0:ℝ)..1, x^4*thetaSecondMode x) ≤ (38627/153600000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_upper_4_000 thetaTenth_second_cell_upper_4_001) (add_le_add thetaTenth_second_cell_upper_4_002 thetaTenth_second_cell_upper_4_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_lower_6 :
    (39/573440000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^6*thetaSecondMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_lower_6_000 thetaTenth_second_cell_lower_6_001) (add_le_add thetaTenth_second_cell_lower_6_002 thetaTenth_second_cell_lower_6_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_upper_6 :
    (∫ x in (0:ℝ)..1, x^6*thetaSecondMode x) ≤ (103203/4587520000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_upper_6_000 thetaTenth_second_cell_upper_6_001) (add_le_add thetaTenth_second_cell_upper_6_002 thetaTenth_second_cell_upper_6_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_lower_8 :
    (61/23592960000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^8*thetaSecondMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_lower_8_000 thetaTenth_second_cell_lower_8_001) (add_le_add thetaTenth_second_cell_lower_8_002 thetaTenth_second_cell_lower_8_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_upper_8 :
    (∫ x in (0:ℝ)..1, x^8*thetaSecondMode x) ≤ (271367/23592960000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_upper_8_000 thetaTenth_second_cell_upper_8_001) (add_le_add thetaTenth_second_cell_upper_8_002 thetaTenth_second_cell_upper_8_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_lower_10 :
    (13/115343360000000000:ℝ) ≤ (∫ x in (0:ℝ)..1, x^10*thetaSecondMode x) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_lower_10_000 thetaTenth_second_cell_lower_10_001) (add_le_add thetaTenth_second_cell_lower_10_002 thetaTenth_second_cell_lower_10_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem thetaTenth_second_integral_upper_10 :
    (∫ x in (0:ℝ)..1, x^10*thetaSecondMode x) ≤ (25245731/2768240640000000000:ℝ) := by
  have h := (add_le_add (add_le_add thetaTenth_second_cell_upper_10_000 thetaTenth_second_cell_upper_10_001) (add_le_add thetaTenth_second_cell_upper_10_002 thetaTenth_second_cell_upper_10_003))
  rw [thetaTenth_second_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

end
end CarrySelfAdjointOperator

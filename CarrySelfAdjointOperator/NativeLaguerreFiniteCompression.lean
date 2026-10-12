import CarrySelfAdjointOperator.NativeCauchyLaguerreExactGram

/-! Compression algebra and the R=0 canary in the ORIGINAL interval Lp.
No identification of the full Laguerre operator is assumed. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace ComplexOrder unitInterval
open MeasureTheory
noncomputable section
set_option autoImplicit false

def compressionLeakage {N : ℕ} (P A : Matrix (Fin N) (Fin N) ℂ) :=
  P*A*(1-P)*A*P

theorem compression_square {N : ℕ} (P A : Matrix (Fin N) (Fin N) ℂ)
    (hP : P*P=P) : P*A^2*P = (P*A*P)^2 + compressionLeakage P A := by
  have hs : (P*A*P)^2 = P*A*(P*P)*A*P := by noncomm_ring
  rw [hs, hP]
  unfold compressionLeakage
  noncomm_ring

theorem compression_polynomial {N : ℕ} (P A : Matrix (Fin N) (Fin N) ℂ)
    (hP : P*P=P) : P*(1-A)^2*P = (P-P*A*P)^2 + compressionLeakage P A := by
  have hl : P*(P*A*P)=P*A*P := by simp only [← Matrix.mul_assoc, hP]
  have hr : (P*A*P)*P=P*A*P := by simp only [Matrix.mul_assoc, hP]
  calc
    _ = P-P*A*P-P*A*P+P*A^2*P := by
      simp only [pow_two, sub_mul, mul_sub, one_mul, mul_one, hP]
      noncomm_ring
    _ = P-P*A*P-P*A*P+(P*A*P)^2+compressionLeakage P A := by
      rw [compression_square P A hP]
      abel
    _ = (P-P*A*P)^2+compressionLeakage P A := by
      simp only [pow_two, sub_mul, mul_sub, hP, hl, hr]
      noncomm_ring

/-- Compression of the whole polynomial precedes substitution of the
compressed advance. Scalar q enters through B=qA, without a fitted metric. -/
theorem compression_scaled_polynomial {N : ℕ} (P A : Matrix (Fin N) (Fin N) ℂ)
    (hP : P*P=P) (q : ℂ) :
    P*(1-q • A)^2*P = (P-q • (P*A*P))^2 + q^2 • compressionLeakage P A := by
  have h := compression_polynomial P (q • A) hP
  simpa only [compressionLeakage, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, pow_two] using h

theorem compressionLeakage_eq_gram {N : ℕ} (P A : Matrix (Fin N) (Fin N) ℂ)
    (hP : P*P=P) (hPs : Pᴴ=P) (hA : Aᴴ=A) :
    compressionLeakage P A = ((1-P)*A*P)ᴴ * ((1-P)*A*P) := by
  have hc : (1-P)*(1-P)=1-P := by
    calc
      _ = 1-P-P+P*P := by noncomm_ring
      _ = 1-P := by rw [hP]; noncomm_ring
  calc
    compressionLeakage P A = P*A*((1-P)*(1-P))*A*P := by rw [hc]; rfl
    _ = ((1-P)*A*P)ᴴ * ((1-P)*A*P) := by
      simp [Matrix.conjTranspose_mul, hA, hPs, Matrix.mul_assoc]

theorem compressionLeakage_posSemidef {N : ℕ} (P A : Matrix (Fin N) (Fin N) ℂ)
    (hP : P*P=P) (hPs : Pᴴ=P) (hA : Aᴴ=A) :
    (compressionLeakage P A).PosSemidef := by
  rw [compressionLeakage_eq_gram P A hP hPs hA]
  exact Matrix.posSemidef_conjTranspose_mul_self _

def intervalMonomial (n : ℕ) : C(unitInterval, ℂ) where
  toFun u := ((u : ℝ) : ℂ)^n
  continuous_toFun := by fun_prop

def intervalMonomialLp (n : ℕ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  ContinuousMap.toLp 2 volume ℂ (intervalMonomial n)

theorem inner_intervalMonomialLp (i j : ℕ) :
    inner ℂ (intervalMonomialLp i) (intervalMonomialLp j) =
      ((((i+j+1 : ℕ) : ℝ)⁻¹) : ℂ) := by
  rw [intervalMonomialLp, intervalMonomialLp, ContinuousMap.inner_toLp]
  have hi : (fun u : unitInterval => intervalMonomial j u * conj (intervalMonomial i u)) =
      (fun u : unitInterval => (((u : ℝ)^(i+j) : ℝ) : ℂ)) := by
    funext u
    simp [intervalMonomial, ← pow_add, mul_comm]
  rw [hi]
  have hsub : (∫ u : unitInterval, (((u : ℝ)^(i+j) : ℝ) : ℂ)) =
      ∫ u in Set.Icc (0 : ℝ) 1, ((u^(i+j) : ℝ) : ℂ) := by
    simpa [unitInterval.volume_def] using
      (MeasureTheory.integral_subtype_comap (μ := (volume : Measure ℝ))
        measurableSet_Icc (fun u : ℝ => ((u^(i+j) : ℝ) : ℂ)))
  rw [hsub]
  have hs : (∫ u in Set.Icc (0 : ℝ) 1, ((u^(i+j) : ℝ) : ℂ)) =
      ∫ u in (0 : ℝ)..1, ((u^(i+j) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [hs, intervalIntegral.integral_ofReal, integral_pow]
  norm_num

/-- Constant Laguerre order zero and its first two radial advances, in Lp. -/
theorem compression_R0_radial_moments :
    inner ℂ (intervalMonomialLp 0) (intervalMonomialLp 0) = 1 ∧
    inner ℂ (intervalMonomialLp 0) (intervalMonomialLp 1) = 1/2 ∧
    inner ℂ (intervalMonomialLp 0) (intervalMonomialLp 2) = 1/3 := by
  rw [inner_intervalMonomialLp, inner_intervalMonomialLp, inner_intervalMonomialLp]
  norm_num

theorem compression_R0_leakage :
    inner ℂ (intervalMonomialLp 1 - (1/2 : ℂ) • intervalMonomialLp 0)
      (intervalMonomialLp 1 - (1/2 : ℂ) • intervalMonomialLp 0) = 1/12 := by
  rw [inner_sub_left]
  simp only [inner_sub_right, inner_smul_left, inner_smul_right, inner_intervalMonomialLp]
  norm_num
  ring

/-- The true R=0, q=1/2 valve compression is computed BEFORE truncation. -/
theorem compression_R0_valve :
    inner ℂ (intervalMonomialLp 0)
      ((2 : ℂ) • intervalMonomialLp 0 - (2 : ℂ) • intervalMonomialLp 1 +
        (1/2 : ℂ) • intervalMonomialLp 2) = 7/6 := by
  simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_intervalMonomialLp]
  norm_num

theorem compression_R0_naive_and_gap :
    (2 : ℚ)*(1-(1/2)*(1/2))^2 = 9/8 ∧ (7/6 : ℚ)-9/8=1/24 := by norm_num

end
end CarrySelfAdjointOperator.NativeLaguerre

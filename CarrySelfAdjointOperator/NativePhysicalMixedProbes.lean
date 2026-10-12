import CarrySelfAdjointOperator.NativePhysicalTwoPortChart

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open NativeLaguerre
noncomputable section
set_option autoImplicit false

def secondPortDefect (N : ℕ) (theta v wG : Fin N → ℂ) : Fin N → ℂ :=
  wG - fun j => theta j * v j

def mixedPhysicalProbes (N k : ℕ) (theta d : Fin N → ℂ) : Fin N → ℂ :=
  fun a => canonicalCompletedNativeProjectiveChiralForm
    (twoPortSynthesis N k (Pi.single a 1)
      (fun j => theta j * (Pi.single a (1 : ℂ) : Fin N → ℂ) j))
    (twoPortSynthesis N k 0 d)

def mixedProbeScale (k : ℕ) : ℂ := -Complex.I*((k : ℂ)+1)/2

theorem mixedPhysicalProbes_formula (N k : ℕ) (theta d : Fin N → ℂ) :
    mixedPhysicalProbes N k theta d = mixedProbeScale k • ((cauchyMatrix N) *ᵥ d) := by
  funext a
  rw [mixedPhysicalProbes, twoPort_signed_form]
  simp only [matrixPairing, Matrix.mulVec_zero, dotProduct_zero, Pi.smul_apply, smul_eq_mul]
  have he : star (Pi.single a (1 : ℂ)) ⬝ᵥ ((cauchyMatrix N) *ᵥ d) =
      ((cauchyMatrix N) *ᵥ d) a := by
    simp [dotProduct, Pi.single_apply]
  rw [he]
  unfold mixedProbeScale
  ring

theorem mixedProbeScale_ne_zero (k : ℕ) : mixedProbeScale k ≠ 0 := by
  have hK : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  unfold mixedProbeScale
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hK) (by norm_num)

/-- Positive definiteness of the ORIGINAL Cauchy Gram detects all vector
coordinates; no fitted observation metric is introduced. -/
theorem mixedPhysicalProbes_faithful (N k : ℕ) (theta d : Fin N → ℂ) :
    (∀ a, mixedPhysicalProbes N k theta d a = 0) ↔ d = 0 := by
  rw [← funext_iff]
  change (mixedPhysicalProbes N k theta d = (0 : Fin N → ℂ)) ↔ d = 0
  rw [mixedPhysicalProbes_formula, smul_eq_zero_iff_right (mixedProbeScale_ne_zero k)]
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr (cauchyMatrix_posDef N).isUnit
  exact ⟨fun h => hi (h.trans (Matrix.mulVec_zero _).symm), fun h => by simp [h]⟩

theorem mixedPhysicalProbes_decode (N k : ℕ) (theta d : Fin N → ℂ) :
    d = (2*Complex.I/((k : ℂ)+1)) •
      ((cauchyMatrix N)⁻¹ *ᵥ mixedPhysicalProbes N k theta d) := by
  have hu : IsUnit (cauchyMatrix N).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (cauchyMatrix_posDef N).isUnit
  rw [mixedPhysicalProbes_formula, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, smul_smul]
  have hcoef : 2*Complex.I/((k : ℂ)+1) * mixedProbeScale k = 1 := by
    have hK : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    unfold mixedProbeScale
    field_simp
    simp
  rw [hcoef, one_smul]

theorem mixedPhysicalProbes_diagnostic (N k : ℕ) (theta d : Fin N → ℂ) :
    matrixPairing (cauchyMatrix N)⁻¹
      (mixedPhysicalProbes N k theta d) (mixedPhysicalProbes N k theta d) =
      (((k : ℂ)+1)^2/4) * matrixPairing (cauchyMatrix N) d d := by
  have hu : IsUnit (cauchyMatrix N).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (cauchyMatrix_posDef N).isUnit
  have hh := (cauchyMatrix_posDef N).isHermitian
  rw [mixedPhysicalProbes_formula]
  unfold matrixPairing
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mulVec]
  simp only [star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, RCLike.star_def]
  have he : star ((cauchyMatrix N) *ᵥ d) ⬝ᵥ d =
      star d ⬝ᵥ ((cauchyMatrix N) *ᵥ d) := by
    rw [Matrix.star_mulVec, hh.eq, ← Matrix.dotProduct_mulVec]
  rw [he]
  unfold mixedProbeScale
  simp only [map_div₀, map_mul, map_neg, Complex.conj_I, map_add,
    map_one, Complex.conj_natCast, map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem diagonalDefect_autopairing_zero (N k : ℕ) (d e : Fin N → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k 0 d) (twoPortSynthesis N k 0 e) = 0 := by
  rw [twoPort_signed_form]
  simp [matrixPairing]

theorem nonzeroDiagonalDefect_detected (N k : ℕ) (theta d : Fin N → ℂ) (hd : d ≠ 0) :
    ∃ a, mixedPhysicalProbes N k theta d a ≠ 0 := by
  by_contra h
  apply hd
  apply (mixedPhysicalProbes_faithful N k theta d).mp
  simpa using h

theorem realConstantGauge_preserves_graph_form (N k : ℕ) (theta v w : Fin N → ℂ) (c : ℝ) :
    canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v (fun j => (theta j+(c : ℂ))*v j))
      (twoPortSynthesis N k w (fun j => (theta j+(c : ℂ))*w j)) =
    canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v (fun j => theta j*v j))
      (twoPortSynthesis N k w (fun j => theta j*w j)) := by
  rw [twoPort_signed_form, twoPort_signed_form]
  unfold matrixPairing Matrix.mulVec
  simp only [dotProduct]
  simp only [Pi.star_apply, RCLike.star_def, map_mul, map_add, Complex.conj_ofReal,
    Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realConstantGauge_detected (N k : ℕ) (theta v : Fin N → ℂ)
    (c : ℝ) (hc : c ≠ 0) (hv : v ≠ 0) :
    ∃ a, mixedPhysicalProbes N k theta
      (secondPortDefect N theta v (fun j => (theta j+(c : ℂ))*v j)) a ≠ 0 := by
  apply nonzeroDiagonalDefect_detected
  have he : secondPortDefect N theta v (fun j => (theta j+(c : ℂ))*v j) = (c : ℂ) • v := by
    funext j
    simp only [secondPortDefect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact smul_ne_zero (by exact_mod_cast hc) hv

end
end CarrySelfAdjointOperator.PhysicalSewing

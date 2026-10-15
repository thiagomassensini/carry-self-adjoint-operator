import CarrySelfAdjointOperator.NativeCompletedSourceTwoPositiveChannels

/-! Iteration of the exact source reduction, with the complete residual.
The sequence is defined from the completed source, independently of a target
Gram and of a finite dimension. Positive identification of a prefix requires
the displayed source-scale signs. No all-stage sign or limit is postulated. -/
namespace CarrySelfAdjointOperator.SourcePositiveReduction
open Filter
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def responseAxis (f : ℂ → ℂ) : ℂ → ℂ := dslope f 0

def responseScale (f : ℂ → ℂ) : ℝ := (responseAxis f 0).re

def sourceReduction (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  dslope (responseAxis f) 0 z / ((responseScale f : ℂ)*responseAxis f z)

/-- A single source-defined chain. Total division does not certify regularity
or positivity at a stage with a zero or negative scale. -/
def chainResponse : ℕ → ℂ → ℂ
  | 0 => sourceResponse
  | n+1 => sourceReduction (chainResponse n)

def chainAxis (n : ℕ) : ℂ → ℂ := responseAxis (chainResponse n)

def chainScale (n : ℕ) : ℝ := responseScale (chainResponse n)

def chainKernel (n : ℕ) (z w : ℂ) : ℂ :=
  (chainResponse n w-conj (chainResponse n z))/(w-conj z)

def chainWeight : ℕ → ℂ → ℂ
  | 0, _ => 1
  | n+1, z => chainWeight n z*chainResponse n z

/-- A channel is indexed by its stage, never by a finite prefix length. -/
def chainChannel (n : ℕ) (z : ℂ) : ℂ :=
  chainWeight n z*chainAxis n z/(Real.sqrt (chainScale n) : ℂ)

def chainPrefixKernel (n : ℕ) (z w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, conj (chainChannel j z)*chainChannel j w

theorem chainAxis_zero_eq (z : ℂ) : chainAxis 0 z = sourceAxis z :=
  (sourceAxis_eq_dslope z).symm

theorem chainScale_zero_eq : chainScale 0 = sourceScale := by
  change (chainAxis 0 0).re = _
  rw [chainAxis_zero_eq]
  rfl

theorem chainResponse_one_eq : chainResponse 1 = reducedResponse := by
  have he : responseAxis sourceResponse = sourceAxis := funext (fun z =>
    (sourceAxis_eq_dslope z).symm)
  funext z
  change sourceReduction sourceResponse z = _
  simp only [sourceReduction, responseScale, he, sourceScale, reducedResponse]

theorem chainAxis_one_eq (z : ℂ) : chainAxis 1 z = secondAxis z := by
  simp only [chainAxis, responseAxis, chainResponse_one_eq, secondAxis]

theorem chainScale_one_eq : chainScale 1 = reducedSourceScale := by
  change (chainAxis 1 0).re = _
  rw [chainAxis_one_eq, secondAxis, dslope_same]
  rfl

theorem chainResponse_two_eq : chainResponse 2 = secondReducedResponse := by
  have he : responseAxis (chainResponse 1) = secondAxis := funext chainAxis_one_eq
  funext z
  change sourceReduction (chainResponse 1) z = _
  change dslope (responseAxis (chainResponse 1)) 0 z /
    ((chainScale 1 : ℂ)*responseAxis (chainResponse 1) z) = _
  rw [he, chainScale_one_eq]
  rfl

theorem chainResponse_eq_mul_axis (n : ℕ) (hzero : chainResponse n 0 = 0) (z : ℂ) :
    chainResponse n z = z*chainAxis n z := by
  have h := sub_smul_dslope (chainResponse n) 0 z
  simpa only [sub_zero, hzero, smul_eq_mul, chainAxis, responseAxis] using h.symm

/-- Exact relation used at each stage; it asks for source values, never for
a desired kernel, a moment Gram, or an energy-positivity hypothesis. -/
theorem chainReduction_source_equation (n : ℕ)
    (hzero : chainResponse n 0 = 0)
    (hreal : chainAxis n 0 = (chainScale n : ℂ)) (hpos : 0 < chainScale n)
    (z : ℂ) (hz : chainAxis n z ≠ 0) :
    chainResponse n z*chainResponse (n+1) z = chainAxis n z/(chainScale n : ℂ)-1 := by
  have ha : (chainScale n : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have h := sub_smul_dslope (chainAxis n) 0 z
  simp only [sub_zero, smul_eq_mul, hreal] at h
  rw [chainResponse_eq_mul_axis n hzero]
  change (z*chainAxis n z) * (dslope (chainAxis n) 0 z /
    ((chainScale n : ℂ)*chainAxis n z)) = _
  field_simp
  linear_combination h

/-- Exact reconstruction at every regular positive-scale stage. -/
theorem chainResponse_reconstruction (n : ℕ)
    (hzero : chainResponse n 0 = 0)
    (hreal : chainAxis n 0 = (chainScale n : ℂ)) (hpos : 0 < chainScale n)
    (z : ℂ) (hz : chainAxis n z ≠ 0) :
    chainResponse n z*(1-(chainScale n : ℂ)*z*chainResponse (n+1) z) =
      (chainScale n : ℂ)*z := by
  have h := chainReduction_source_equation n hzero hreal hpos z hz
  have ha : (chainScale n : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have he := chainResponse_eq_mul_axis n hzero z
  field_simp at h
  linear_combination -z*h + he

/-- Off the removable center, this is the same reciprocal reduction at
every stage. No moments or target Gram enter the definition of its input. -/
theorem chainResponse_reciprocal (n : ℕ)
    (hzero : chainResponse n 0 = 0)
    (hreal : chainAxis n 0 = (chainScale n : ℂ)) (hpos : 0 < chainScale n)
    (z : ℂ) (hz0 : z ≠ 0) (hz : chainAxis n z ≠ 0) :
    chainResponse (n+1) z = 1/((chainScale n : ℂ)*z)-1/chainResponse n z := by
  have ha : (chainScale n : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  change dslope (chainAxis n) 0 z/((chainScale n : ℂ)*chainAxis n z) = _
  rw [dslope_of_ne _ hz0, chainResponse_eq_mul_axis n hzero z]
  simp only [slope, sub_zero, smul_eq_mul, hreal, vsub_eq_sub]
  field_simp [ha, hz0, hz]

theorem chainKernel_step (n : ℕ)
    (hzero : chainResponse n 0 = 0)
    (hreal : chainAxis n 0 = (chainScale n : ℂ)) (hpos : 0 < chainScale n)
    (z w : ℂ) (hz : chainAxis n z ≠ 0) (hw : chainAxis n w ≠ 0)
    (hsep : w ≠ conj z) :
    chainKernel n z w = conj (chainAxis n z)*chainAxis n w/(chainScale n : ℂ) +
      conj (chainResponse n z)*chainResponse n w*chainKernel (n+1) z w := by
  have hzw := chainReduction_source_equation n hzero hreal hpos w hw
  have hzz := congrArg conj (chainReduction_source_equation n hzero hreal hpos z hz)
  simp only [map_mul, map_sub, map_div₀, map_one, Complex.conj_ofReal] at hzz
  have hnum : chainResponse n w-conj (chainResponse n z) =
      (w-conj z)*(conj (chainAxis n z)*chainAxis n w/(chainScale n : ℂ)) +
      conj (chainResponse n z)*chainResponse n w*
        (chainResponse (n+1) w-conj (chainResponse (n+1) z)) := by
    rw [chainResponse_eq_mul_axis n hzero w,
      chainResponse_eq_mul_axis n hzero z, map_mul] at *
    linear_combination -(conj z*conj (chainAxis n z))*hzw + (w*chainAxis n w)*hzz
  unfold chainKernel
  rw [hnum]
  field_simp [sub_ne_zero.mpr hsep]

theorem chainChannel_pair (n : ℕ) (hpos : 0 < chainScale n) (z w : ℂ) :
    conj (chainChannel n z)*chainChannel n w =
      conj (chainWeight n z)*chainWeight n w*
        (conj (chainAxis n z)*chainAxis n w/(chainScale n : ℂ)) := by
  have hsq : (Real.sqrt (chainScale n) : ℂ)^2 = (chainScale n : ℂ) := by
    exact_mod_cast Real.sq_sqrt hpos.le
  simp only [chainChannel, map_div₀, map_mul, Complex.conj_ofReal]
  rw [div_mul_div_comm]
  rw [← pow_two, hsq]
  ring

theorem chainChannel_zero_eq (z : ℂ) : chainChannel 0 z = positiveFeature z := by
  simp only [chainChannel, chainWeight, chainAxis_zero_eq, chainScale_zero_eq, one_mul,
    positiveFeature]

theorem chainChannel_one_eq (z : ℂ) :
    chainChannel 1 z = sourceResponse z*secondPositiveFeature z := by
  simp only [chainChannel, chainWeight, chainResponse, chainAxis_one_eq,
    chainScale_one_eq, one_mul, secondPositiveFeature]
  ring

theorem chainPrefixKernel_succ (n : ℕ) (z w : ℂ) :
    chainPrefixKernel (n+1) z w = chainPrefixKernel n z w +
      conj (chainChannel n z)*chainChannel n w := Finset.sum_range_succ _ _

/-- The chain literally extends the two-channel realization of PR #98. -/
theorem chainPrefix_two_eq_existing (z w : ℂ) :
    chainPrefixKernel 2 z w = inner ℂ (positivePair z) (positivePair w) := by
  simp only [chainPrefixKernel, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    chainChannel_zero_eq, chainChannel_one_eq, map_mul]
  rw [positivePair_inner]
  simp only [RCLike.inner_apply]
  ring

/-- Arbitrarily long finite prefixes, with one unchanged chain and the
complete residual. The source-scale conditions remain explicit and finite. -/
theorem chainKernel_prefix (n : ℕ)
    (hzero : ∀ j < n, chainResponse j 0 = 0)
    (hreal : ∀ j < n, chainAxis j 0 = (chainScale j : ℂ))
    (hpos : ∀ j < n, 0 < chainScale j)
    (z w : ℂ) (hz : ∀ j < n, chainAxis j z ≠ 0)
    (hw : ∀ j < n, chainAxis j w ≠ 0) (hsep : w ≠ conj z) :
    chainKernel 0 z w = chainPrefixKernel n z w +
      conj (chainWeight n z)*chainWeight n w*chainKernel n z w := by
  induction n with
  | zero => simp [chainPrefixKernel, chainWeight]
  | succ n ih =>
    have hn : ∀ j < n, j < n+1 := fun j hj => Nat.lt_trans hj (Nat.lt_succ_self n)
    have hi := ih (fun j hj => hzero j (hn j hj)) (fun j hj => hreal j (hn j hj))
      (fun j hj => hpos j (hn j hj)) (fun j hj => hz j (hn j hj))
      (fun j hj => hw j (hn j hj))
    calc
      _ = chainPrefixKernel n z w +
          conj (chainWeight n z)*chainWeight n w*chainKernel n z w := hi
      _ = _ := by
        rw [chainKernel_step n (hzero n (by omega)) (hreal n (by omega))
          (hpos n (by omega)) z w (hz n (by omega)) (hw n (by omega)) hsep,
          chainPrefixKernel_succ, chainChannel_pair n (hpos n (by omega))]
        simp only [chainWeight, map_mul]
        ring

/-- Exact depth of the source factor multiplying the residual. No remainder
is erased and no uniform estimate in the depth is inferred from this factor. -/
theorem chainWeight_factor (n : ℕ) (hzero : ∀ j < n, chainResponse j 0 = 0) (z : ℂ) :
    chainWeight n z = z^n * ∏ j ∈ Finset.range n, chainAxis j z := by
  induction n with
  | zero => simp [chainWeight]
  | succ n ih =>
    rw [chainWeight, ih (fun j hj => hzero j (by omega)),
      chainResponse_eq_mul_axis n (hzero n (by omega)), Finset.prod_range_succ, pow_succ]
    ring

private theorem scalar_finite_gram {N : ℕ} (c v : Fin N → ℂ) :
    ∑ i, ∑ j, conj (c i)*c j*(conj (v i)*v j) =
      (Complex.normSq (∑ i, c i*v i) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual sum-of-squares energy for any finite number of channels and any
finite number of inputs, with every input crossing retained. -/
theorem chainPrefix_finite_energy (n : ℕ) {N : ℕ} (c : Fin N → ℂ) (z : Fin N → ℂ) :
    ∑ i, ∑ j, conj (c i)*c j*chainPrefixKernel n (z i) (z j) =
      ((∑ k ∈ Finset.range n, Complex.normSq (∑ i, c i*chainChannel k (z i)) : ℝ) : ℂ) := by
  induction n with
  | zero => simp [chainPrefixKernel]
  | succ n ih =>
    simp only [chainPrefixKernel_succ, mul_add, Finset.sum_add_distrib,
      Finset.sum_range_succ, Complex.ofReal_add]
    rw [ih, scalar_finite_gram]

/-- The full original finite energy: a literal sum of positive channel
energies plus the complete residual with its ORIGINAL input weights. -/
theorem chainKernel_finite_energy (n : ℕ)
    (hzero : ∀ j < n, chainResponse j 0 = 0)
    (hreal : ∀ j < n, chainAxis j 0 = (chainScale j : ℂ))
    (hpos : ∀ j < n, 0 < chainScale j) {N : ℕ}
    (c : Fin N → ℂ) (z : Fin N → ℂ)
    (haxis : ∀ i, ∀ j < n, chainAxis j (z i) ≠ 0)
    (hsep : ∀ i j, z j ≠ conj (z i)) :
    ∑ i, ∑ j, conj (c i)*c j*chainKernel 0 (z i) (z j) =
      ((∑ k ∈ Finset.range n, Complex.normSq (∑ i, c i*chainChannel k (z i)) : ℝ) : ℂ) +
        ∑ i, ∑ j, conj (c i*chainWeight n (z i))*(c j*chainWeight n (z j))*
          chainKernel n (z i) (z j) := by
  rw [← chainPrefix_finite_energy]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [chainKernel_prefix n hzero hreal hpos (z i) (z j) (haxis i) (haxis j) (hsep i j), map_mul]
  ring

theorem chainPrefix_finite_energy_nonneg (n : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (z : Fin N → ℂ) :
    0 ≤ (∑ i, ∑ j, conj (c i)*c j*chainPrefixKernel n (z i) (z j)).re := by
  rw [chainPrefix_finite_energy, Complex.ofReal_re]
  exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

end
end CarrySelfAdjointOperator.SourcePositiveReduction

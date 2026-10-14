import CarrySelfAdjointOperator.CompletedNativeChiralReturnEnergyPort

/-!
# Two source-derived energy channels, before the sign is known

The positive and negative parts of I-T* T act on the original incident span.
Their ports live in the existing L2 of the unit interval. The full signed
pairing is exact in all finite dimensions. A positive representation in the
boundary limit requires that the negative channel disappear; this is kept as
an explicit unproved geometric obligation, not an assumed moment Gram.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The measure already belongs to the original Cauchy carrier. -/
theorem physicalCauchy_norm_sq_eq_integral (f : CanonicalCompletedNativeChiralCauchyCarrier) :
    ‖f‖^2 = ∫ t : unitInterval, ‖f t‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ]
  change (∫ t : unitInterval, inner ℂ (f t) (f t)).re = _
  have hi : (∫ t : unitInterval, inner ℂ (f t) (f t)).re =
      ∫ t : unitInterval, (inner ℂ (f t) (f t)).re := by
    convert (integral_re (𝕜 := ℂ)
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)).symm using 1 <;> rfl
  rw [hi]
  apply integral_congr_ae
  filter_upwards [] with t
  convert (norm_sq_eq_re_inner (𝕜 := ℂ) (f t)).symm using 1
  rfl

/-- Vanishing of the whole finite negative channel is exactly the old finite
return estimate. It does not constitute a new reason for its sign. -/
theorem radialReturnJordanNegativePort_zero_iff_contractive (k N : ℕ) :
    radialReturnJordanNegativePort k N = 0 ↔ ‖radialReturnTransfer k N‖ ≤ 1 := by
  constructor
  · intro hz
    apply (radialReturnTransfer_norm_le_one_iff_storage k N).mpr
    intro c
    have h := radialReturnJordanPorts_storage k N c
    simp only [hz, zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero] at h
    rw [← h]
    exact sq_nonneg _
  · exact radialReturnJordanNegativePort_eq_zero k N

/-- The complete original source in the positive Jordan channel. -/
def nativeSourceJordanPositiveState (n k : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialReturnJordanPositivePort k (2*n)
    (radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k x))

/-- Its negative companion, with exactly the same source input. -/
def nativeSourceJordanNegativeState (n k : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialReturnJordanNegativePort k (2*n)
    (radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k x))

/-- Unconditional signed energy limit of the original source, at every fixed
finite order. No positivity or convergence of either vector is assumed. -/
theorem nativeSourceJordan_signed_energy_tendsto (n : ℕ) (x : Fin (2*n) → ℂ) :
    Tendsto (fun k => 2 * (‖nativeSourceJordanPositiveState n k x‖^2 -
      ‖nativeSourceJordanNegativeState n k x‖^2)) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x)) := by
  have hs : Tendsto (fun k => 2 * (storage k (nativeSourceChiralJetInput n k x) 1).re)
      atTop (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x)) := by
    simpa only [nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage] using
      nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto n x
  simpa only [nativeSourceJordanPositiveState, nativeSourceJordanNegativeState,
    radialReturnJordanPorts_storage] using hs

/-- A source-facing geometric target: disappearance of the actual negative
channel transfers the limiting energy to the positive port. -/
theorem nativeSourceJordan_positive_energy_tendsto_of_no_negative_leak
    (n : ℕ) (x : Fin (2*n) → ℂ)
    (hnegative : Tendsto (fun k => ‖nativeSourceJordanNegativeState n k x‖)
      atTop (nhds 0)) :
    Tendsto (fun k => 2 * ‖nativeSourceJordanPositiveState n k x‖^2) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x)) := by
  have hn := (hnegative.pow 2).const_mul (2 : ℝ)
  have h := (nativeSourceJordan_signed_energy_tendsto n x).add hn
  have he (k : ℕ) :
      2 * (‖nativeSourceJordanPositiveState n k x‖^2 -
        ‖nativeSourceJordanNegativeState n k x‖^2) +
        2 * ‖nativeSourceJordanNegativeState n k x‖^2 =
      2 * ‖nativeSourceJordanPositiveState n k x‖^2 := by ring
  simpa only [he, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using h

/-- Nonnegativity follows from the no-leak target, without a desired Gram
identity as premise. The no-leak target itself is not proved here. -/
theorem nativeSourceBoundary_nonneg_of_no_negative_leak
    (n : ℕ) (x : Fin (2*n) → ℂ)
    (hnegative : Tendsto (fun k => ‖nativeSourceJordanNegativeState n k x‖)
      atTop (nhds 0)) : 0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x := by
  apply ge_of_tendsto (nativeSourceJordan_positive_energy_tendsto_of_no_negative_leak
    n x hnegative)
  exact Eventually.of_forall (fun k => mul_nonneg (by norm_num) (sq_nonneg _))

/-- If the physical positive states converge as vectors and the negative
channel disappears, the native boundary is literally their physical energy. -/
theorem nativeSourceBoundary_eq_physical_energy_of_state_limits
    (n : ℕ) (x : Fin (2*n) → ℂ)
    (v : CanonicalCompletedNativeChiralCauchyCarrier)
    (hpositive : Tendsto (fun k => nativeSourceJordanPositiveState n k x) atTop (nhds v))
    (hnegative : Tendsto (fun k => ‖nativeSourceJordanNegativeState n k x‖)
      atTop (nhds 0)) : nativeSourceFiniteBoundaryEnergy (2*n) x = 2*‖v‖^2 := by
  exact tendsto_nhds_unique
    (nativeSourceJordan_positive_energy_tendsto_of_no_negative_leak n x hnegative)
    ((hpositive.norm.pow 2).const_mul (2 : ℝ))

/-- The positive measure is the original unit-interval volume. Constructing
the limits, rather than selecting a convenient measure, is the open step. -/
theorem nativeSourceBoundary_eq_integral_of_state_limits
    (n : ℕ) (x : Fin (2*n) → ℂ)
    (v : CanonicalCompletedNativeChiralCauchyCarrier)
    (hpositive : Tendsto (fun k => nativeSourceJordanPositiveState n k x) atTop (nhds v))
    (hnegative : Tendsto (fun k => ‖nativeSourceJordanNegativeState n k x‖)
      atTop (nhds 0)) :
    nativeSourceFiniteBoundaryEnergy (2*n) x = 2 * ∫ t : unitInterval, ‖v t‖^2 := by
  rw [nativeSourceBoundary_eq_physical_energy_of_state_limits n x v hpositive hnegative,
    physicalCauchy_norm_sq_eq_integral]

/-- Non-collapse of the limiting positive source supplies strict positivity. -/
theorem nativeSourceBoundary_pos_of_state_limits
    (n : ℕ) (x : Fin (2*n) → ℂ)
    (v : CanonicalCompletedNativeChiralCauchyCarrier)
    (hpositive : Tendsto (fun k => nativeSourceJordanPositiveState n k x) atTop (nhds v))
    (hnegative : Tendsto (fun k => ‖nativeSourceJordanNegativeState n k x‖)
      atTop (nhds 0)) (hv : v ≠ 0) :
    0 < nativeSourceFiniteBoundaryEnergy (2*n) x := by
  rw [nativeSourceBoundary_eq_physical_energy_of_state_limits n x v hpositive hnegative]
  exact mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hv))

private theorem source_port_basis_expansion (n k : ℕ) (x : Fin (2*n) → ℂ)
    (P : RadialIncidentSpan k (2*n) →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier) :
    P (radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k x)) =
      ∑ i : Fin (2*n), x i • P (radialIncidentVector k (2*n)
        (nativeSourceChiralJetInput n k (Pi.single i 1))) := by
  classical
  let B := P.toLinearMap.comp
    ((radialIncidentCoordinates k (2*n)).symm.toLinearMap.comp (nativeSourceChiralJetInput n k))
  have hx : (∑ i : Fin (2*n), x i • Pi.single i (1 : ℂ)) = x := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
  change B x = ∑ i : Fin (2*n), x i • B (Pi.single i 1)
  conv_lhs => rw [← hx]
  rw [map_sum]
  simp only [map_smul]

/-- The positive state retains the original linear superposition law. -/
theorem nativeSourceJordanPositiveState_basis (n k : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceJordanPositiveState n k x =
      ∑ i : Fin (2*n), x i • nativeSourceJordanPositiveState n k (Pi.single i 1) :=
  source_port_basis_expansion n k x _

/-- The negative correction retains the same superposition and all crosses. -/
theorem nativeSourceJordanNegativeState_basis (n k : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceJordanNegativeState n k x =
      ∑ i : Fin (2*n), x i • nativeSourceJordanNegativeState n k (Pi.single i 1) :=
  source_port_basis_expansion n k x _

/-- A single proposed physical column family, independent of dimension,
determines the limits of all finite whole-source positive syntheses. -/
theorem nativeSourceJordanPositiveState_tendsto_of_columns
    (n : ℕ) (x : Fin (2*n) → ℂ) (phi : ℕ → CanonicalCompletedNativeChiralCauchyCarrier)
    (hcolumns : ∀ i : Fin (2*n),
      Tendsto (fun k => nativeSourceJordanPositiveState n k (Pi.single i 1))
        atTop (nhds (phi i.val))) :
    Tendsto (fun k => nativeSourceJordanPositiveState n k x) atTop
      (nhds (∑ i : Fin (2*n), x i • phi i.val)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ => (hcolumns i).const_smul (x i))
  simpa only [← nativeSourceJordanPositiveState_basis] using h

/-- Basis-column no-leak controls every whole-source input, before readout. -/
theorem nativeSourceJordanNegativeState_norm_tendsto_of_columns
    (n : ℕ) (x : Fin (2*n) → ℂ)
    (hcolumns : ∀ i : Fin (2*n),
      Tendsto (fun k => ‖nativeSourceJordanNegativeState n k (Pi.single i 1)‖)
        atTop (nhds 0)) :
    Tendsto (fun k => ‖nativeSourceJordanNegativeState n k x‖) atTop (nhds 0) := by
  have hi (i : Fin (2*n)) :
      Tendsto (fun k => x i • nativeSourceJordanNegativeState n k (Pi.single i 1))
        atTop (nhds (0 : CanonicalCompletedNativeChiralCauchyCarrier)) := by
    have hv : Tendsto (fun k => nativeSourceJordanNegativeState n k (Pi.single i 1))
        atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (hcolumns i)
    simpa using hv.const_smul (x i)
  have h := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hv : Tendsto (fun k => nativeSourceJordanNegativeState n k x) atTop (nhds 0) := by
    simpa only [← nativeSourceJordanNegativeState_basis, Finset.sum_const_zero] using h
  simpa using hv.norm

/-- The requested one-family integral representation follows from PHYSICAL
column limits and disappearance of their negative companion. These are
explicit open hypotheses, not a desired moment Gram or a chosen measure. -/
theorem nativeSourceBoundary_integral_of_coherent_columns
    (phi : ℕ → CanonicalCompletedNativeChiralCauchyCarrier)
    (hpositive : ∀ n : ℕ, ∀ i : Fin (2*n),
      Tendsto (fun k => nativeSourceJordanPositiveState n k (Pi.single i 1))
        atTop (nhds (phi i.val)))
    (hnegative : ∀ n : ℕ, ∀ i : Fin (2*n),
      Tendsto (fun k => ‖nativeSourceJordanNegativeState n k (Pi.single i 1)‖)
        atTop (nhds 0)) (n : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceFiniteBoundaryEnergy (2*n) x =
      2 * ∫ t : unitInterval, ‖(∑ i : Fin (2*n), x i • phi i.val) t‖^2 := by
  exact nativeSourceBoundary_eq_integral_of_state_limits n x _
    (nativeSourceJordanPositiveState_tendsto_of_columns n x phi (hpositive n))
    (nativeSourceJordanNegativeState_norm_tendsto_of_columns n x (hnegative n))

/-- Adding a zero final boundary coefficient preserves the native energy. -/
theorem nativeSourceFiniteBoundaryEnergy_snoc_zero (N : ℕ) (x : Fin N → ℂ) :
    nativeSourceFiniteBoundaryEnergy (N+1) (Fin.snoc x 0) =
      nativeSourceFiniteBoundaryEnergy N x := by
  rw [nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum,
    nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum]
  simp [Fin.sum_univ_castSucc]

/-- Coherent physical column limits give ONE fixed-measure representation at
every finite N, including odd N. Existence of these limits remains open. -/
theorem nativeSourceBoundary_integral_all_N_of_coherent_columns
    (phi : ℕ → CanonicalCompletedNativeChiralCauchyCarrier)
    (hpositive : ∀ n : ℕ, ∀ i : Fin (2*n),
      Tendsto (fun k => nativeSourceJordanPositiveState n k (Pi.single i 1))
        atTop (nhds (phi i.val)))
    (hnegative : ∀ n : ℕ, ∀ i : Fin (2*n),
      Tendsto (fun k => ‖nativeSourceJordanNegativeState n k (Pi.single i 1)‖)
        atTop (nhds 0)) (N : ℕ) (x : Fin N → ℂ) :
    nativeSourceFiniteBoundaryEnergy N x =
      2 * ∫ t : unitInterval, ‖(∑ i : Fin N, x i • phi i.val) t‖^2 := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' N
  · exact nativeSourceBoundary_integral_of_coherent_columns phi hpositive hnegative n x
  · have h := nativeSourceBoundary_integral_of_coherent_columns phi hpositive hnegative (n+1)
    have he : 2*(n+1) = (2*n+1)+1 := by omega
    rw [he] at h
    have hp := h (Fin.snoc x 0)
    rw [nativeSourceFiniteBoundaryEnergy_snoc_zero] at hp
    simpa [Fin.sum_univ_castSucc] using hp

/-- Both Jordan channels use the OLD signed jet coefficients. -/
def radialReturnJordanPositiveJet (k N : ℕ) (a : Fin N) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  (Real.sqrt 2 : ℂ)⁻¹ • radialReturnJordanPositivePort k N
    (radialIncidentVector k N (radialDifferenceSourceCoefficients k N a.val))

def radialReturnJordanNegativeJet (k N : ℕ) (a : Fin N) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  (Real.sqrt 2 : ℂ)⁻¹ • radialReturnJordanNegativePort k N
    (radialIncidentVector k N (radialDifferenceSourceCoefficients k N a.val))

/-- Full polarized jet identity, including the negative Gram correction. -/
theorem radialReturnJordanJets_pairing (k N : ℕ) (a b : Fin N) :
    inner ℂ (radialReturnJordanPositiveJet k N a) (radialReturnJordanPositiveJet k N b) -
      inner ℂ (radialReturnJordanNegativeJet k N a) (radialReturnJordanNegativeJet k N b) =
        canonicalCompletedNativeProjectiveChiralForm
          (projectiveChiralDifferenceJet k a.val) (projectiveChiralDifferenceJet k b.val) := by
  have hscale : conj ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rfl
  simp only [radialReturnJordanPositiveJet, radialReturnJordanNegativeJet,
    inner_smul_left, inner_smul_right, ← mul_assoc]
  rw [mul_comm ((Real.sqrt 2 : ℂ)⁻¹) (conj ((Real.sqrt 2 : ℂ)⁻¹)), hscale]
  rw [← mul_sub, radialReturnJordanPorts_pairing,
    radialReturnTransfer_exact, radialReturnTransfer_exact]
  rw [← radialDifferenceSource_pair k N a.val a.isLt,
    ← radialDifferenceSource_pair k N b.val b.isLt]
  rfl

/-- Disappearance of the negative vector norms controls ALL off-diagonal
corrections by continuity of the physical inner product. -/
theorem radialReturnJordanNegativeJet_inner_tendsto_zero (N : ℕ) (a b : Fin N)
    (ha : Tendsto (fun k => ‖radialReturnJordanNegativeJet k N a‖) atTop (nhds 0))
    (hb : Tendsto (fun k => ‖radialReturnJordanNegativeJet k N b‖) atTop (nhds 0)) :
    Tendsto (fun k => inner ℂ (radialReturnJordanNegativeJet k N a)
      (radialReturnJordanNegativeJet k N b)) atTop (nhds 0) := by
  have hva : Tendsto (fun k => radialReturnJordanNegativeJet k N a) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr ha
  have hvb : Tendsto (fun k => radialReturnJordanNegativeJet k N b) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hb
  simpa using hva.inner (𝕜 := ℂ) hvb

/-- The native full coefficient block is recovered if the ACTUAL negative
channel disappears on the corresponding jets. No finite-step contraction
or positivity of target moments is assumed in this limit theorem. -/
theorem radialReturnJordanPositiveJet_inner_tendsto_of_no_negative_leak
    (N : ℕ) (a b : Fin N)
    (ha : Tendsto (fun k => ‖radialReturnJordanNegativeJet k N a‖) atTop (nhds 0))
    (hb : Tendsto (fun k => ‖radialReturnJordanNegativeJet k N b‖) atTop (nhds 0)) :
    Tendsto (fun k => inner ℂ (radialReturnJordanPositiveJet k N a)
      (radialReturnJordanPositiveJet k N b)) atTop
      (nhds (polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment
        a.val b.val)) := by
  have h := (projectiveChiralDifferenceJet_pairing_tendsto_coefficient a.val b.val).add
    (radialReturnJordanNegativeJet_inner_tendsto_zero N a b ha hb)
  have he (k : ℕ) :
      canonicalCompletedNativeProjectiveChiralForm
        (projectiveChiralDifferenceJet k a.val) (projectiveChiralDifferenceJet k b.val) +
        inner ℂ (radialReturnJordanNegativeJet k N a) (radialReturnJordanNegativeJet k N b) =
      inner ℂ (radialReturnJordanPositiveJet k N a) (radialReturnJordanPositiveJet k N b) := by
    rw [← radialReturnJordanJets_pairing k N a b]
    ring
  simpa only [he, add_zero] using h

/-- Seven-source check: no negative channel survives eventually, using the
already proved source return estimate. -/
theorem radialReturnJordanNegativePort_seven_eventually_zero :
    ∀ᶠ k : ℕ in atTop, radialReturnJordanNegativePort k 7 = 0 := by
  filter_upwards [radialReturnTransfer_seven_eventually_norm_le_one] with k hk
  exact radialReturnJordanNegativePort_eq_zero k 7 hk

end
end CarrySelfAdjointOperator.ChiralReturn

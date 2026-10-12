import CarrySelfAdjointOperator.NativeIntervalMultiplier
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Compression of the actual radial operator onto any finite Laguerre span.
No all-order orthogonality or completeness assumption is used. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped unitInterval InnerProductSpace
noncomputable section
set_option autoImplicit false

def laguerreFiniteSpan (R : ℕ) : Submodule ℂ CanonicalCompletedNativeChiralCauchyCarrier :=
  Submodule.span ℂ (Set.range (fun r : Fin (R+1) => laguerreMode r.val))

instance laguerreFiniteSpan_finiteDimensional (R : ℕ) : FiniteDimensional ℂ (laguerreFiniteSpan R) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

def laguerreFiniteProjection (R : ℕ) := (laguerreFiniteSpan R).starProjection

theorem laguerreFiniteProjection_idempotent (R : ℕ) :
    (laguerreFiniteProjection R) * (laguerreFiniteProjection R) = (laguerreFiniteProjection R) :=
  (laguerreFiniteSpan R).isIdempotentElem_starProjection

theorem laguerreFiniteProjection_isSelfAdjoint (R : ℕ) : IsSelfAdjoint (laguerreFiniteProjection R) :=
  isSelfAdjoint_starProjection _

theorem laguerreFiniteProjection_mode (R : ℕ) (r : Fin (R+1)) :
    (laguerreFiniteProjection R) (laguerreMode r.val) = laguerreMode r.val := by
  apply (laguerreFiniteSpan R).starProjection_eq_self_iff.mpr
  exact Submodule.subset_span (Set.mem_range_self r)

/-- The actual loss through the orthogonal complement, for every finite cutoff. -/
def physicalFiniteLeakage (R : ℕ) :=
  (laguerreFiniteProjection R) * physicalRadialAdvance * (1-(laguerreFiniteProjection R)) *
    physicalRadialAdvance * (laguerreFiniteProjection R)

theorem physicalFinite_compression_square (R : ℕ) :
    (laguerreFiniteProjection R) * physicalRadialAdvance^2 * (laguerreFiniteProjection R) =
      ((laguerreFiniteProjection R) * physicalRadialAdvance * (laguerreFiniteProjection R))^2 +
        (physicalFiniteLeakage R) := by
  have hs : ((laguerreFiniteProjection R) * physicalRadialAdvance *
      (laguerreFiniteProjection R))^2 =
      (laguerreFiniteProjection R) * physicalRadialAdvance *
      ((laguerreFiniteProjection R) * (laguerreFiniteProjection R)) *
      physicalRadialAdvance * (laguerreFiniteProjection R) := by noncomm_ring
  rw [hs, laguerreFiniteProjection_idempotent R]
  unfold physicalFiniteLeakage
  noncomm_ring

theorem physicalFiniteLeakage_eq_gram (R : ℕ) :
    (physicalFiniteLeakage R) =
      star ((1-(laguerreFiniteProjection R))*physicalRadialAdvance*(laguerreFiniteProjection R)) *
        ((1-(laguerreFiniteProjection R))*physicalRadialAdvance*(laguerreFiniteProjection R)) := by
  have hc : (1-(laguerreFiniteProjection R))*(1-(laguerreFiniteProjection R)) =
      1-(laguerreFiniteProjection R) := by
    calc
      _ = 1-(laguerreFiniteProjection R)-(laguerreFiniteProjection R)+
        (laguerreFiniteProjection R)*(laguerreFiniteProjection R) := by noncomm_ring
      _ = _ := by rw [laguerreFiniteProjection_idempotent R]; noncomm_ring
  simp only [star_mul, star_sub, star_one,
    physicalRadialAdvance_isSelfAdjoint.star_eq,
    (laguerreFiniteProjection_isSelfAdjoint R).star_eq]
  calc
    (physicalFiniteLeakage R) = (laguerreFiniteProjection R)*physicalRadialAdvance*
      ((1-(laguerreFiniteProjection R))*(1-(laguerreFiniteProjection R)))*
      physicalRadialAdvance*(laguerreFiniteProjection R) := by rw [hc]; rfl
    _ = _ := by noncomm_ring

theorem physicalFiniteLeakage_isPositive (R : ℕ) : (physicalFiniteLeakage R).IsPositive := by
  rw [physicalFiniteLeakage_eq_gram R]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- The input outside the compression is retained explicitly, for every physical h. -/
theorem physicalFinite_outside_input (R : ℕ)
    (h : CanonicalCompletedNativeChiralCauchyCarrier) :
    (laguerreFiniteProjection R) ((physicalRadialAdvance^2) h) =
      (((laguerreFiniteProjection R)*physicalRadialAdvance*(laguerreFiniteProjection R))^2) h +
      (physicalFiniteLeakage R) h +
      ((laguerreFiniteProjection R)*physicalRadialAdvance^2*(1-(laguerreFiniteProjection R)) :
        CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier) h := by
  have he : (laguerreFiniteProjection R)*physicalRadialAdvance^2 =
      (laguerreFiniteProjection R)*physicalRadialAdvance^2*(laguerreFiniteProjection R) +
      (laguerreFiniteProjection R)*physicalRadialAdvance^2*(1-(laguerreFiniteProjection R)) := by
    noncomm_ring
  rw [physicalFinite_compression_square R] at he
  exact congrArg (fun T => T h) he

/-- The complete valve polynomial is compressed first, for every cutoff. -/
theorem physicalFinite_valve_compression (R : ℕ) (q : ℂ) :
    laguerreFiniteProjection R * (1-q • physicalRadialAdvance)^2 * laguerreFiniteProjection R =
      (laguerreFiniteProjection R-q • (laguerreFiniteProjection R*physicalRadialAdvance*
        laguerreFiniteProjection R))^2 + q^2 • physicalFiniteLeakage R := by
  let P := laguerreFiniteProjection R
  let A := q • physicalRadialAdvance
  have hP : P*P=P := laguerreFiniteProjection_idempotent R
  have hs : (P*A*P)^2 = P*A*(P*P)*A*P := by noncomm_ring
  have hl : P*(P*A*P)=P*A*P := by simp only [← mul_assoc, hP]
  have hr : (P*A*P)*P=P*A*P := by simp only [mul_assoc, hP]
  have hleak : P*A^2*P = (P*A*P)^2+P*A*(1-P)*A*P := by
    rw [hs, hP]
    noncomm_ring
  have he : P*(1-A)^2*P = (P-P*A*P)^2+P*A*(1-P)*A*P := by
    calc
      _ = P-P*A*P-P*A*P+P*A^2*P := by
        simp only [pow_two, sub_mul, mul_sub, one_mul, mul_one, hP]
        noncomm_ring
      _ = P-P*A*P-P*A*P+(P*A*P)^2+P*A*(1-P)*A*P := by rw [hleak]; abel
      _ = _ := by simp only [pow_two, sub_mul, mul_sub, hP, hl, hr]; noncomm_ring
  simpa only [P, A, physicalFiniteLeakage, smul_mul_assoc, mul_smul_comm,
    smul_smul, pow_two] using he


/-- The physical TFVD valve, with its fixed q inverse normalization. -/
def physicalValveOperator (q : ℂ) : CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ]
    CanonicalCompletedNativeChiralCauchyCarrier := q⁻¹ • (1-q • physicalRadialAdvance)^2

theorem physicalFinite_scaled_valve_compression (R : ℕ) (q : ℂ) (hq : q ≠ 0) :
    laguerreFiniteProjection R * physicalValveOperator q * laguerreFiniteProjection R =
      q⁻¹ • (laguerreFiniteProjection R-q • (laguerreFiniteProjection R*physicalRadialAdvance*
        laguerreFiniteProjection R))^2 + q • physicalFiniteLeakage R := by
  have hqq : q⁻¹*q^2=q := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  simp only [physicalValveOperator, mul_smul_comm, smul_mul_assoc,
    physicalFinite_valve_compression, smul_add, smul_smul, hqq]

/-- The outside-input term for the whole valve, not just for its quadratic part. -/
theorem physicalFinite_valve_outside_input (R : ℕ) (q : ℂ) (hq : q ≠ 0)
    (h : CanonicalCompletedNativeChiralCauchyCarrier) :
    laguerreFiniteProjection R (physicalValveOperator q h) =
      (q⁻¹ • (laguerreFiniteProjection R-q • (laguerreFiniteProjection R*physicalRadialAdvance*
        laguerreFiniteProjection R))^2) h + (q • physicalFiniteLeakage R) h +
      (laguerreFiniteProjection R*physicalValveOperator q*(1-laguerreFiniteProjection R) :
        CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier) h := by
  have he : laguerreFiniteProjection R*physicalValveOperator q =
      laguerreFiniteProjection R*physicalValveOperator q*laguerreFiniteProjection R +
      laguerreFiniteProjection R*physicalValveOperator q*(1-laguerreFiniteProjection R) := by
    noncomm_ring
  rw [physicalFinite_scaled_valve_compression R q hq] at he
  exact congrArg (fun T => T h) he

/-! The previously certified three-mode API is retained as the R=2 specialization. -/
def firstThreeLaguerreSpan := laguerreFiniteSpan 2

instance firstThreeLaguerreSpan_finiteDimensional : FiniteDimensional ℂ firstThreeLaguerreSpan :=
  laguerreFiniteSpan_finiteDimensional 2

def firstThreeLaguerreProjection := laguerreFiniteProjection 2

theorem firstThreeLaguerreProjection_idempotent :
    firstThreeLaguerreProjection * firstThreeLaguerreProjection = firstThreeLaguerreProjection :=
  laguerreFiniteProjection_idempotent 2

theorem firstThreeLaguerreProjection_isSelfAdjoint : IsSelfAdjoint firstThreeLaguerreProjection :=
  laguerreFiniteProjection_isSelfAdjoint 2

theorem firstThreeLaguerreProjection_mode (r : Fin 3) :
    firstThreeLaguerreProjection (laguerreMode r.val) = laguerreMode r.val :=
  laguerreFiniteProjection_mode 2 r

def physicalFirstThreeLeakage := physicalFiniteLeakage 2

theorem physicalFirstThree_compression_square :
    firstThreeLaguerreProjection * physicalRadialAdvance^2 * firstThreeLaguerreProjection =
      (firstThreeLaguerreProjection * physicalRadialAdvance * firstThreeLaguerreProjection)^2 +
        physicalFirstThreeLeakage :=
  physicalFinite_compression_square 2

theorem physicalFirstThreeLeakage_eq_gram :
    physicalFirstThreeLeakage =
      star ((1-firstThreeLaguerreProjection)*physicalRadialAdvance*firstThreeLaguerreProjection) *
        ((1-firstThreeLaguerreProjection)*physicalRadialAdvance*firstThreeLaguerreProjection) :=
  physicalFiniteLeakage_eq_gram 2

theorem physicalFirstThreeLeakage_isPositive : physicalFirstThreeLeakage.IsPositive :=
  physicalFiniteLeakage_isPositive 2

theorem physicalFirstThree_outside_input
    (h : CanonicalCompletedNativeChiralCauchyCarrier) :
    firstThreeLaguerreProjection ((physicalRadialAdvance^2) h) =
      ((firstThreeLaguerreProjection*physicalRadialAdvance*firstThreeLaguerreProjection)^2) h +
      physicalFirstThreeLeakage h +
      (firstThreeLaguerreProjection*physicalRadialAdvance^2*(1-firstThreeLaguerreProjection) :
        CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier) h :=
  physicalFinite_outside_input 2 h

end
end CarrySelfAdjointOperator.NativeLaguerre

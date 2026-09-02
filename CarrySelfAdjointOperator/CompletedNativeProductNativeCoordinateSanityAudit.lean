import CarrySelfAdjointOperator.CompletedNativeLocalProductGreenAudit
import Mathlib.Tactic

/-!
# Center sanity check for the native coordinate of the product carrier

Before constructing a coupled xi/native Green kernel, this file checks the
necessary center-energy inequality for the native coordinate already used by
the product ledger.  The calculation is entirely upstream of any xi state.

At the centered parameter the two finite C3 port legs coincide.  The
canonical `sqrt 2 * G(0)` normalization therefore leaves exactly the energy
of one ordinary finite C3 leg divided by `‖G(0)‖²`.
-/

open scoped ComplexConjugate InnerProductSpace BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- At the centered height the native scalar denominator is the classical
zeta value at `1 / 2`. -/
theorem nativeHeightScalar_zero_eq_riemannZeta_half :
    nativeHeightScalar 0 = riemannZeta (1 / 2 : ℂ) := by
  unfold nativeHeightScalar
  rw [nativeScalar_eq_riemannZeta]
  · norm_num [operatorHeightParameter]
  · constructor <;> norm_num [operatorHeightParameter]

/-- The phase-normalized and ordinary legs of the finite C3 port coincide at
the centered parameter. -/
theorem finiteC3GenuineBracketGreenBoundaryPair_zero_fst_eq_snd :
    (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
        (operatorHeightParameter 0)).1 =
      (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
        (operatorHeightParameter 0)).2 := by
  ext n
  rw [finiteC3GenuineBracketGreenBoundaryPair_fst_eq_radial_mul_completedPrefix,
    finiteC3GenuineBracketGreenBoundaryPair_snd_eq_completedPrefix]
  norm_num [operatorHeightParameter, criticalDisplacement]

/-- The raw Hilbert C3 port has twice the energy of either one of its equal
center legs. -/
theorem norm_sq_canonicalCompletedOperatorC3HilbertState_zero :
    ‖canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 =
      2 *
        ‖(NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter 0)).2‖ ^ 2 := by
  have h :=
    inner_canonicalCompletedOperatorC3HilbertState_eq_finiteC3PositiveGram 0 0
  rw [finiteC3GenuineBracketGreenBoundaryPair_zero_fst_eq_snd] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  have hreal :
      ‖canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 =
        ‖(NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter 0)).2‖ ^ 2 +
          ‖(NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter 0)).2‖ ^ 2 := by
    exact_mod_cast h
  linarith

/-- Coordinate expansion of the one surviving finite C3 leg. -/
theorem norm_sq_finiteC3GenuineBracketGreenBoundaryPair_zero_snd :
    ‖(NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
        (operatorHeightParameter 0)).2‖ ^ 2 =
      ∑ n : Fin 3,
        ‖positiveDirichletGradient (1 / 2 : ℂ) n‖ ^ 2 := by
  let v :=
    (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
      (operatorHeightParameter 0)).2
  have hcomplex :
      ((‖v‖ ^ 2 : ℝ) : ℂ) =
        ∑ n : Fin 3, ((‖v n‖ ^ 2 : ℝ) : ℂ) := by
    calc
      ((‖v‖ ^ 2 : ℝ) : ℂ) = ((‖v‖ : ℂ) ^ 2) := by norm_cast
      _ = inner ℂ v v := (inner_self_eq_norm_sq_to_K v).symm
      _ = ∑ n : Fin 3, inner ℂ (v n) (v n) := by
        rw [PiLp.inner_apply]
      _ = ∑ n : Fin 3, ((‖v n‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
  have hreal :
      ‖v‖ ^ 2 = ∑ n : Fin 3, ‖v n‖ ^ 2 := by
    exact_mod_cast hcomplex
  simpa [v, operatorHeightParameter] using hreal

/-- Exact normalization formula for the native coordinate `g₀` in the
product ledger. -/
theorem norm_sq_normalizedCompletedNativeC3State_zero :
    ‖normalizedCompletedGreenState
        nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 =
      ‖canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 /
        (2 * ‖nativeHeightScalar 0‖ ^ 2) := by
  have hG : ‖nativeHeightScalar 0‖ ≠ 0 :=
    norm_ne_zero_iff.mpr nativeHeightScalar_zero_ne_zero
  have hsqrt : ‖(((Real.sqrt 2 : ℝ) : ℂ))‖ ^ 2 = 2 := by
    simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg 2),
      Real.sq_sqrt]
  unfold normalizedCompletedGreenState
  rw [norm_smul, mul_pow, norm_inv, norm_mul]
  field_simp [hG]
  rw [hsqrt]
  ring

/-- The center Gram is exactly the energy of one ordinary finite C3 leg,
divided by the native scalar energy.  The factor `2` from the two equal port
legs is cancelled by the canonical `sqrt 2` normalization. -/
theorem norm_sq_normalizedCompletedNativeC3State_zero_eq_finiteLeg :
    ‖normalizedCompletedGreenState
        nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 =
      ‖(NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
          (operatorHeightParameter 0)).2‖ ^ 2 /
        ‖nativeHeightScalar 0‖ ^ 2 := by
  rw [norm_sq_normalizedCompletedNativeC3State_zero,
    norm_sq_canonicalCompletedOperatorC3HilbertState_zero]
  ring

/-- Fully coordinate-level formula for the center Gram of the native product
coordinate. -/
theorem norm_sq_normalizedCompletedNativeC3State_zero_eq_finThreeSum :
    ‖normalizedCompletedGreenState
        nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 =
      (∑ n : Fin 3,
          ‖positiveDirichletGradient (1 / 2 : ℂ) n‖ ^ 2) /
        ‖nativeHeightScalar 0‖ ^ 2 := by
  rw [norm_sq_normalizedCompletedNativeC3State_zero_eq_finiteLeg,
    norm_sq_finiteC3GenuineBracketGreenBoundaryPair_zero_snd]

/-- The same exact coordinate formula with its scalar denominator identified
as the classical central zeta value. -/
theorem norm_sq_normalizedCompletedNativeC3State_zero_eq_zeta_finThreeSum :
    ‖normalizedCompletedGreenState
        nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 =
      (∑ n : Fin 3,
          ‖positiveDirichletGradient (1 / 2 : ℂ) n‖ ^ 2) /
        ‖riemannZeta (1 / 2 : ℂ)‖ ^ 2 := by
  rw [norm_sq_normalizedCompletedNativeC3State_zero_eq_finThreeSum,
    nativeHeightScalar_zero_eq_riemannZeta_half]

/-- Any Hilbert realization whose product-dressed center Gram is `h₀` must
leave at most `h₀` energy in the already-fixed native coordinate.  This
necessary inequality is independent of the choice of the xi carrier or xi
state. -/
theorem norm_sq_normalizedCompletedNativeC3State_zero_le_h0_of_productGram
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hcenter :
      inner ℂ
          (canonicalCompletedNativeNormalizedGreenState xiState 0)
          (canonicalCompletedNativeNormalizedGreenState xiState 0) =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) :
    ‖normalizedCompletedGreenState
        nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0‖ ^ 2 ≤
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hsum :
      inner ℂ
          (normalizedCompletedGreenState
            nativeXiCompletionFactor xiState 0)
          (normalizedCompletedGreenState
            nativeXiCompletionFactor xiState 0) +
        inner ℂ
          (normalizedCompletedGreenState
            nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0)
          (normalizedCompletedGreenState
            nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0) =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
    rw [← inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_factorGrams]
    exact hcenter
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_re] at hre
  simp only [Complex.coe_algebraMap, pow_two, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
  nlinarith [sq_nonneg
    ‖normalizedCompletedGreenState nativeXiCompletionFactor xiState 0‖]

end

end CarrySelfAdjointOperator

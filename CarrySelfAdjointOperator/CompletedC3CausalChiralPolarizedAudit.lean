import CarrySelfAdjointOperator.CompletedC3CausalChiralSourceCoherence
import CarrySelfAdjointOperator.CompletedC3AmbientRadialTiltSamplePositivity
import Mathlib.Tactic

/-!
# Polarized audit of the causal chiral block

The diagonal coisometric sewing compares

`sqrt (2 * Im z) * ambientResponse(z) \oplus negativeChirality(z)`

with the positive Wronskian chirality.  For the moment problem this comparison
must be polarized before Taylor extraction.  This module performs that
polarization with the exact completed-characteristic normalization.

The resulting two-variable identity records an important distinction.  On
the diagonal the ambient coefficient is `2 * Im z`, but off the diagonal the
Wronskian coefficient is `w - conj z`.  These agree only after the canonical
quarter turn on the diagonal; they are not the same two-variable Gram weight.
No positivity, zero, sewing, or spectral hypothesis is used.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Characteristic-normalized coisometric block -/

/-- The coisometric chiral state with exactly the normalization used by the
completed logarithmic response.  Its first coordinate is the normalized
source-matched ambient response; its second coordinate is the normalized
negative Wronskian chirality. -/
def canonicalCompletedC3NormalizedCoisometricChiralState
    (M : ℕ) (z : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    CanonicalCompletedC3CoisometricChiralEnergyCarrier :=
  WithLp.toLp 2
    ((((Real.sqrt (2 * z.im) : ℝ) : ℂ) •
        canonicalCompletedC3NormalizedAmbientResponseState z hzHalf),
      canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M z)

/-- Positive Hilbert kernel of the normalized enlarged coisometric block. -/
def canonicalCompletedC3NormalizedCoisometricChiralKernel
    (M : ℕ) (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
    (canonicalCompletedC3NormalizedCoisometricChiralState M z hzHalf)
    (canonicalCompletedC3NormalizedCoisometricChiralState M w hwHalf)

/-- The enlarged kernel is the orthogonal sum of the scaled normalized
ambient Gram and the negative normalized chiral Gram. -/
theorem canonicalCompletedC3NormalizedCoisometricChiralKernel_eq
    (M : ℕ) (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3NormalizedCoisometricChiralKernel
        M z w hzHalf hwHalf =
      (((Real.sqrt (2 * z.im) : ℝ) : ℂ) *
          ((Real.sqrt (2 * w.im) : ℝ) : ℂ)) *
        canonicalCompletedC3NormalizedAmbientResponseKernel
          z w hzHalf hwHalf +
      canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
        M z w := by
  unfold canonicalCompletedC3NormalizedCoisometricChiralKernel
    canonicalCompletedC3NormalizedCoisometricChiralState
  rw [WithLp.prod_inner_apply]
  rw [inner_smul_left, inner_smul_right]
  rw [← canonicalCompletedC3NormalizedAmbientResponseKernel_eq_inner]
  simp only [Complex.conj_ofReal]
  simp [canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel]
  ring

/-- Every finite sample of the enlarged normalized block is positive
semidefinite because it is an ordinary Hilbert Gram matrix. -/
theorem canonicalCompletedC3NormalizedCoisometricChiralKernel_posSemidef
    {ι : Type*} [Finite ι]
    (M : ℕ) (point : ι → ℂ)
    (hhalf : ∀ i, 0 < (operatorHeightParameter (point i)).re) :
    (Matrix.of fun i j =>
      canonicalCompletedC3NormalizedCoisometricChiralKernel
        M (point i) (point j) (hhalf i) (hhalf j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i =>
    canonicalCompletedC3NormalizedCoisometricChiralState
      M (point i) (hhalf i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-! ## Exact comparison with the completed-native divided slope -/

/-- The signed difference of the full normalized chiral kernels is exactly
the spectral separation multiplying the completed-native `dslope`. -/
theorem canonicalCompletedC3NormalizedFullChiralDifference_eq_mul_dslope
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    Complex.I *
        (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
            M z w -
          canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
            M z w) =
      (w - conj z) *
        canonicalCompletedNativePolarizedDslopeKernel z w := by
  calc
    Complex.I *
          (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
              M z w -
            canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
              M z w) =
        Complex.I *
          (completedNativeNormalizedPositiveChiralTraceKernel z w -
            completedNativeNormalizedNegativeChiralTraceKernel z w) :=
      canonicalCompletedC3FullChiralBalance_eq_scalarChiralBalance
        M hzStrip hwStrip hzF hwF
    _ = (w - conj z) *
          canonicalCompletedNativePolarizedDslopeKernel z w :=
      completedNativeScalarChiralDifference_eq_separation_mul_dslope
        hzStrip hzF hwF hsep

/-- Polarizing the diagonal norm comparison produces this exact formula.
The first coefficient is the separable square-root Gram weight, whereas the
second is the Hermitian spectral separation.  Their diagonal agreement does
not identify them off the diagonal. -/
theorem canonicalCompletedC3NormalizedCoisometricChiralKernel_sub_positive_eq
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedCoisometricChiralKernel
          M z w hzStrip.1 hwStrip.1 -
        canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
          M z w =
      (((Real.sqrt (2 * z.im) : ℝ) : ℂ) *
          ((Real.sqrt (2 * w.im) : ℝ) : ℂ)) *
        canonicalCompletedC3NormalizedAmbientResponseKernel
          z w hzStrip.1 hwStrip.1 +
      Complex.I * (w - conj z) *
        canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [canonicalCompletedC3NormalizedCoisometricChiralKernel_eq]
  have hchiral :=
    canonicalCompletedC3NormalizedFullChiralDifference_eq_mul_dslope
      M hzStrip hwStrip hzF hwF hsep
  have hnegative :
      canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel M z w -
          canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
            M z w =
        Complex.I * ((w - conj z) *
          canonicalCompletedNativePolarizedDslopeKernel z w) := by
    calc
      _ = -(canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
              M z w -
            canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
              M z w) := by ring
      _ = (Complex.I * Complex.I) *
            (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
                M z w -
              canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
                M z w) := by rw [Complex.I_mul_I]; ring
      _ = Complex.I * (Complex.I *
            (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
                M z w -
              canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
                M z w)) := by ring
      _ = _ := by rw [hchiral]
  rw [show
      (((Real.sqrt (2 * z.im) : ℝ) : ℂ) *
            ((Real.sqrt (2 * w.im) : ℝ) : ℂ)) *
          canonicalCompletedC3NormalizedAmbientResponseKernel
            z w hzStrip.1 hwStrip.1 +
          canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
            M z w -
          canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
            M z w =
        (((Real.sqrt (2 * z.im) : ℝ) : ℂ) *
            ((Real.sqrt (2 * w.im) : ℝ) : ℂ)) *
          canonicalCompletedC3NormalizedAmbientResponseKernel
            z w hzStrip.1 hwStrip.1 +
          (canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
              M z w -
            canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
              M z w) by ring,
    hnegative]
  ring

/-- The separable square-root weight of the positive coisometric Gram cannot
be the quarter-turned Hermitian separation at two points with distinct real
parts.  Thus the diagonal norm identity has no automatic two-variable
polarization through the same direct-sum state. -/
theorem canonicalCompletedC3CoisometricSqrtWeight_ne_quarterTurnSeparation
    {z w : ℂ} (hre : z.re ≠ w.re) :
    (((Real.sqrt (2 * z.im) : ℝ) : ℂ) *
        ((Real.sqrt (2 * w.im) : ℝ) : ℂ)) ≠
      -Complex.I * (w - conj z) := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.I_re, neg_zero, Complex.neg_im, Complex.I_im,
    neg_one_mul, zero_mul, add_zero, Complex.sub_re, Complex.conj_re] at him
  apply hre
  linarith

/-- On a nonreal upper-half-plane diagonal the polarized block defect reduces
to `2 * Im z` times the honest normalized-kernel mismatch. -/
theorem canonicalCompletedC3NormalizedCoisometricChiralKernel_diagonal_sub_positive_eq
    (M : ℕ) {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    canonicalCompletedC3NormalizedCoisometricChiralKernel
          M z z hzStrip.1 hzStrip.1 -
        canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
          M z z =
      ((2 * z.im : ℝ) : ℂ) *
        (canonicalCompletedC3NormalizedAmbientResponseKernel
            z z hzStrip.1 hzStrip.1 -
          canonicalCompletedNativePolarizedDslopeKernel z z) := by
  rw [canonicalCompletedC3NormalizedCoisometricChiralKernel_sub_positive_eq
    M hzStrip hzStrip hzF hzF (by
      intro h
      exact (ne_of_gt hzIm) (Complex.conj_eq_iff_im.mp h.symm))]
  rw [Complex.sub_conj]
  have hsqrt : (Real.sqrt (2 * z.im)) ^ 2 = 2 * z.im := by
    exact Real.sq_sqrt (by positivity)
  have hsqrtComplex :
      (((Real.sqrt (2 * z.im) : ℝ) : ℂ) ^ 2) =
        ((2 * z.im : ℝ) : ℂ) := by
    exact_mod_cast hsqrt
  rw [show
      ((Real.sqrt (2 * z.im) : ℝ) : ℂ) *
          ((Real.sqrt (2 * z.im) : ℝ) : ℂ) =
        ((Real.sqrt (2 * z.im) : ℝ) : ℂ) ^ 2 by ring,
    hsqrtComplex]
  have hquarterTurn :
      Complex.I * (((2 * z.im : ℝ) : ℂ) * Complex.I) =
        -((2 * z.im : ℝ) : ℂ) := by
    calc
      _ = ((2 * z.im : ℝ) : ℂ) *
          (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hquarterTurn]
  exact (show ∀ c ambient native : ℂ,
      c * ambient + -c * native = c * (ambient - native) by
    intro c ambient native
    ring) _ _ _

/-- Consequently diagonal equality of the two normalized positive blocks is
equivalent to the centered ambient response realizing the native `dslope`.
This is a kernel identity, not a consequence of the coisometry alone. -/
theorem canonicalCompletedC3NormalizedCoisometricChiralKernel_diagonal_eq_positive_iff
    (M : ℕ) {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    canonicalCompletedC3NormalizedCoisometricChiralKernel
          M z z hzStrip.1 hzStrip.1 =
        canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
          M z z ↔
      canonicalCompletedC3NormalizedAmbientResponseKernel
          z z hzStrip.1 hzStrip.1 =
      canonicalCompletedNativePolarizedDslopeKernel z z := by
  have hfactor : ((2 * z.im : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 2 * z.im ≠ 0 by positivity)
  constructor
  · intro hblock
    have hzero :
        ((2 * z.im : ℝ) : ℂ) *
          (canonicalCompletedC3NormalizedAmbientResponseKernel
              z z hzStrip.1 hzStrip.1 -
            canonicalCompletedNativePolarizedDslopeKernel z z) = 0 := by
      rw [←
        canonicalCompletedC3NormalizedCoisometricChiralKernel_diagonal_sub_positive_eq
          M hzStrip hzF hzIm]
      exact sub_eq_zero.mpr hblock
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hfactor)
  · intro hkernel
    apply sub_eq_zero.mp
    rw [canonicalCompletedC3NormalizedCoisometricChiralKernel_diagonal_sub_positive_eq
      M hzStrip hzF hzIm, sub_eq_zero.mpr hkernel, mul_zero]

end

end CarrySelfAdjointOperator

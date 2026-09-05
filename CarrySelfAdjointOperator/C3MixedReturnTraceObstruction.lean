import CarrySelfAdjointOperator.C3MixedReturnSourceTrace

/-!
# Exact source mismatch and residual Gamma trace for the mixed return route

All Gamma vectors below use the existing field and operator. The mixed
projection and its explicitly retained remainder split the same canonical
source. Nonzero remainder energy is not claimed to rule out cross cancellation.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The first mismatch is an explicit Dirichlet-gradient term, not a
renaming of the difference between two unknown kernels. -/
theorem canonicalC3ReturnReadout_sub_dynamicAmplitude
    (cutoff : Fin 6 → ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ nativeScalarDomain) :
    sixCameraReturnReadout (canonicalCompletedC3SixCameraSource z) -
        mixedReturnCompletedCameraReadout cutoff (operatorHeightParameter z) /
          (Real.sqrt 278 : ℂ) =
      ((Real.sqrt 278 / 3 : ℝ) : ℂ) *
          positiveDirichletGradient (operatorHeightParameter z) 1 +
        (4 / (Real.sqrt 278 : ℂ)) *
          (binaryDefectFactor (operatorHeightParameter z) *
            factor 3 (operatorHeightParameter z)) *
          nativeScalar (operatorHeightParameter z) := by
  rw [sixCameraReturnReadout_canonicalSource,
    mixedReturnCompletedCameraReadout_eq_nativeScalar cutoff hs]
  ring

/-- Exact zero-exponent test of the complete camera combination. -/
theorem mixedReturnCompletedCameraReadout_zeroExponent :
    mixedReturnCompletedCameraReadout (fun _ => 0) 0 = 4 := by
  rw [mixedReturnCompletedCameraReadout_eq_four_cameras]
  norm_num [completedNativeCharacteristic, finiteBracketCharacteristic,
    seedDirichletTerm, centerBracketTerm, centeredBracketTerm, dirichletValue,
    FiniteNativeCarryOperator.Camera.radiusSet, FiniteNativeCarryOperator.Camera.halfRange]

/-- A concrete nonzero mismatch at s=0 (z=i/2). This point is in the native
scalar strip, on the boundary of the narrower Genuine critical strip. -/
theorem canonicalC3ReturnReadout_ne_dynamic_at_zeroExponent :
    sixCameraReturnReadout (canonicalCompletedC3SixCameraSource (Complex.I / 2)) ≠
      mixedReturnCompletedCameraReadout (fun _ => 0) 0 / (Real.sqrt 278 : ℂ) := by
  rw [sixCameraReturnReadout_canonicalSource_eq_powers,
    mixedReturnCompletedCameraReadout_zeroExponent]
  have hs : operatorHeightParameter (Complex.I / 2) = 0 := by
    apply Complex.ext <;> norm_num [operatorHeightParameter]
  rw [hs]
  simp only [neg_zero, Complex.cpow_zero, sub_self, mul_zero]
  exact Ne.symm (div_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr (by positivity)))

/-- Additivity of the existing faithful source packing. -/
theorem canonicalC3SixCameraSourceMap_add
    (x y : FiniteC3GreenPortCarrier 3) :
    canonicalC3SixCameraSourceMap (x + y) =
      canonicalC3SixCameraSourceMap x + canonicalC3SixCameraSourceMap y := by
  have hr : canonicalC3RealCameraFinsupp (x + y) =
      canonicalC3RealCameraFinsupp x + canonicalC3RealCameraFinsupp y := by
    simp only [canonicalC3RealCameraFinsupp, Prod.fst_add, Prod.snd_add,
      PiLp.add_apply, Complex.add_re, Finsupp.single_add, Finset.sum_add_distrib]
    abel
  have hi : canonicalC3ImagCameraFinsupp (x + y) =
      canonicalC3ImagCameraFinsupp x + canonicalC3ImagCameraFinsupp y := by
    simp only [canonicalC3ImagCameraFinsupp, Prod.fst_add, Prod.snd_add,
      PiLp.add_apply, Complex.add_im, Finsupp.single_add, Finset.sum_add_distrib]
    abel
  apply WithLp.ofLp_injective 2
  change (cameraEmbedding (canonicalC3RealCameraFinsupp (x+y)),
      cameraEmbedding (canonicalC3ImagCameraFinsupp (x+y))) =
    (cameraEmbedding (canonicalC3RealCameraFinsupp x) +
      cameraEmbedding (canonicalC3RealCameraFinsupp y),
     cameraEmbedding (canonicalC3ImagCameraFinsupp x) +
      cameraEmbedding (canonicalC3ImagCameraFinsupp y))
  rw [hr, hi, map_add, map_add]

/-- Orthogonal return component in the original C3 coefficients. The factor
1/3 follows from Gv=(278/3)e6 and v*Gv=278. -/
def sixCameraMixedReturnPortPart (x : FiniteC3GreenPortCarrier 3) :
    FiniteC3GreenPortCarrier 3 :=
  (WithLp.toLp 2 ![-2 * x.2 1, -x.2 1, (2/3 : ℂ) * x.2 1],
    WithLp.toLp 2 ![0, x.2 1, 0])

/-- This part is exactly the return ray times its Gram projection coefficient. -/
theorem sixCameraMixedReturnPortPart_sourceMap
    (x : FiniteC3GreenPortCarrier 3) :
    canonicalC3SixCameraSourceMap (sixCameraMixedReturnPortPart x) =
      WithLp.toLp 2 (((x.2 1).re / 3) • sixCameraReturnVector,
        ((x.2 1).im / 3) • sixCameraReturnVector) := by
  have hr : canonicalC3RealCameraFinsupp (sixCameraMixedReturnPortPart x) =
      ((x.2 1).re / 3) • sixCameraReturnFinsupp := by
    ext i
    norm_num [canonicalC3RealCameraFinsupp, sixCameraMixedReturnPortPart,
      sixCameraReturnFinsupp, sixCameraMixedReturnRay, Fin.sum_univ_succ,
      Finsupp.single_apply]
    split_ifs <;> ring
  have hi : canonicalC3ImagCameraFinsupp (sixCameraMixedReturnPortPart x) =
      ((x.2 1).im / 3) • sixCameraReturnFinsupp := by
    ext i
    norm_num [canonicalC3ImagCameraFinsupp, sixCameraMixedReturnPortPart,
      sixCameraReturnFinsupp, sixCameraMixedReturnRay, Fin.sum_univ_succ,
      Finsupp.single_apply]
    split_ifs <;> ring
  unfold canonicalC3SixCameraSourceMap sixCameraReturnVector
  rw [hr, hi, map_smul, map_smul]

/-- The normalized projection has the same readout as the full source. -/
theorem sixCameraReturnReadout_portPart
    (x : FiniteC3GreenPortCarrier 3) :
    sixCameraReturnReadout (canonicalC3SixCameraSourceMap (sixCameraMixedReturnPortPart x)) =
      sixCameraReturnReadout (canonicalC3SixCameraSourceMap x) := by
  rw [sixCameraReturnReadout_sourceMap, sixCameraReturnReadout_sourceMap]
  rfl

/-- The complementary port is invisible to the mixed readout. -/
theorem sixCameraReturnReadout_portRemainder
    (x : FiniteC3GreenPortCarrier 3) :
    sixCameraReturnReadout
        (canonicalC3SixCameraSourceMap (x - sixCameraMixedReturnPortPart x)) = 0 := by
  rw [sixCameraReturnReadout_sourceMap]
  simp [sixCameraMixedReturnPortPart]

/-- The camera-5 coefficient (first horizontal coordinate) survives intact
in the complementary canonical port. -/
theorem canonicalC3ReturnPortRemainder_cameraFive (z : ℂ) :
    ((canonicalCompletedOperatorC3State z -
      sixCameraMixedReturnPortPart (canonicalCompletedOperatorC3State z)).2 0) =
      positiveDirichletGradient (operatorHeightParameter z) 0 := by
  simp only [Prod.snd_sub, PiLp.sub_apply]
  simp only [sixCameraMixedReturnPortPart, Matrix.cons_val_zero, sub_zero]
  rw [canonicalCompletedOperatorC3State_eq_greenBoundaryPair,
    finiteC3GenuineBracketGreenBoundaryPair_snd_apply]
  rfl

def canonicalC3ReturnSourcePart (z : ℂ) : RealifiedCameraComplexification :=
  canonicalC3SixCameraSourceMap (sixCameraMixedReturnPortPart (canonicalCompletedOperatorC3State z))

def canonicalC3ReturnSourceRemainder (z : ℂ) : RealifiedCameraComplexification :=
  canonicalC3SixCameraSourceMap
    (canonicalCompletedOperatorC3State z -
      sixCameraMixedReturnPortPart (canonicalCompletedOperatorC3State z))

/-- The full source is retained exactly. -/
theorem canonicalCompletedC3Source_eq_returnPart_add_remainder (z : ℂ) :
    canonicalCompletedC3SixCameraSource z =
      canonicalC3ReturnSourcePart z + canonicalC3ReturnSourceRemainder z := by
  unfold canonicalCompletedC3SixCameraSource canonicalC3ReturnSourcePart
    canonicalC3ReturnSourceRemainder
  rw [← canonicalC3SixCameraSourceMap_add, add_sub_cancel]

/-- The omitted source component is provably nonzero throughout the open
Genuine strip, independently of any scalar-zero hypothesis. -/
theorem canonicalC3ReturnSourceRemainder_ne_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalC3ReturnSourceRemainder z ≠ 0 := by
  intro h
  have hp : canonicalCompletedOperatorC3State z -
      sixCameraMixedReturnPortPart (canonicalCompletedOperatorC3State z) = 0 :=
    canonicalC3SixCameraSourceMap_injective (by
      simpa [canonicalC3ReturnSourceRemainder] using h)
  have hc := congrArg (fun x : FiniteC3GreenPortCarrier 3 => x.2 0) hp
  rw [canonicalC3ReturnPortRemainder_cameraFive] at hc
  exact positiveDirichletGradient_ne_zero_of_mem_genuineCriticalStrip hs 0 hc

/-- The same injective Gamma field preserves this nonzero remainder. -/
theorem canonicalC3ReturnGammaRemainder_energy_pos
    {z : ℂ} (hz : z.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    0 < ‖carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z)‖ ^ 2 := by
  apply pow_pos
  apply norm_pos_iff.mpr
  intro h
  change (carryGammaSource z hz (canonicalC3ReturnSourceRemainder z) :
    WithLp 2 (NaimarkSpace × NaimarkSpace)) = 0 at h
  apply canonicalC3ReturnSourceRemainder_ne_zero hs
  apply carryGammaSource_injective z hz
  simpa using h

/-- Source additivity is transported through the existing Gamma field. -/
theorem canonicalC3GammaState_eq_returnPart_add_remainder
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaState z hz =
      carryGammaComplexState z hz (canonicalC3ReturnSourcePart z) +
        carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z) := by
  change (carryGammaSource z hz (canonicalCompletedC3SixCameraSource z) :
      WithLp 2 (NaimarkSpace × NaimarkSpace)) =
    carryGammaSource z hz (canonicalC3ReturnSourcePart z) +
      carryGammaSource z hz (canonicalC3ReturnSourceRemainder z)
  rw [canonicalCompletedC3Source_eq_returnPart_add_remainder, map_add]

/-- Division-free exact residual for the already named sewing. The two cross
terms and the remainder Gram are retained even though the remainder source
has zero mixed readout. -/
theorem canonicalC3RawGammaWronskianDefect_eq_returnFourTerms
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      (w - conj z) *
        (inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourcePart z))
            (carryGammaComplexState w hw (canonicalC3ReturnSourcePart w)) +
         inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourcePart z))
            (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)) +
         inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
            (carryGammaComplexState w hw (canonicalC3ReturnSourcePart w)) +
         inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
            (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w))) -
        completedGreenWronskian completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z := by
  rw [canonicalCompletedC3RawGammaWronskianDefect,
    canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]
  unfold canonicalCompletedC3PolarizedGammaKernel
  rw [canonicalC3GammaState_eq_returnPart_add_remainder,
    canonicalC3GammaState_eq_returnPart_add_remainder]
  simp only [inner_add_left, inner_add_right]
  ring


set_option maxHeartbeats 600000 in
/-- The raw return defect sees only camera 6. The order is G T - H. -/
theorem sixCameraSlopeDefect_mulVec (c : Fin 6 → ℝ) :
    (sixCameraGram * cameraLogSlopeDiagonal sixCamera - sixCameraFirstMoment) *ᵥ c =
      c 4 • ![(16/3 : ℝ) * (Real.log 6 - Real.log 4),
        6 * (Real.log 6 - Real.log 3),
        (16/3 : ℝ) * (Real.log 6 - Real.log 4), 0, 0, 0] := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.sub_apply, cameraLogSlopeDiagonal, Matrix.mul_diagonal,
      sixCameraGram, sixCameraGramRat, sixCameraFirstMoment, sixCamera, cameraSlope] <;>
    ring_nf <;> rfl

/-- In whitened coordinates the existing return compression annihilates
every coefficient vector with zero camera-6 entry. -/
theorem sixCameraReturnCompression_annihilates_cameraSixZero
    (c : Fin 6 → ℝ) (hc : c 4 = 0) :
    cameraReturnCompression sixCameraGram sixCameraFirstMoment
        (cameraLogSlopeDiagonal sixCamera) *ᵥ (CFC.sqrt sixCameraGram *ᵥ c) = 0 := by
  have hD := sixCameraSlopeDefect_mulVec c
  rw [hc, zero_smul] at hD
  have hHD :
      (sixCameraFirstMoment - sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ c = 0 := by
    rw [Matrix.sub_mulVec] at hD ⊢
    exact sub_eq_zero.mpr (sub_eq_zero.mp hD).symm
  have hunit : IsUnit (CFC.sqrt sixCameraGram) :=
    (sixCameraGram_posDef.isStrictlyPositive.sqrt sixCameraGram).isUnit
  letI := hunit.invertible
  have hinv : positiveInverseSqrt sixCameraGram * CFC.sqrt sixCameraGram = 1 := by
    exact Matrix.inv_mul_of_invertible (CFC.sqrt sixCameraGram)
  have hv : positiveInverseSqrt sixCameraGram *ᵥ (CFC.sqrt sixCameraGram *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  unfold cameraReturnCompression
  simp only [← Matrix.mulVec_mulVec]
  rw [hv, hHD]
  simp

/-- A concrete component of the actual source, invisible to the mixed ray,
produces a nonzero Gamma boundary on every off-axis point in the strip. -/
theorem canonicalC3ReturnRemainder_boundary_ne_zero
    {z : ℂ} (hz : z.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    carryGammaPolarizedBoundaryReadout
        (fun _ => canonicalC3ReturnSourceRemainder z) z z hz hz ≠ 0 := by
  rw [carryGammaPolarizedBoundaryReadout_diagonal_eq_norm_sq]
  apply mul_ne_zero
  · intro h
    apply hz
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  · exact_mod_cast (ne_of_gt (canonicalC3ReturnGammaRemainder_energy_pos hz hs))

/-- No scalar function of the mixed readout alone recovers the existing
Gamma boundary for all sources. The witness is the actual canonical source
remainder versus zero, not a new operator or a finite-rank argument. -/
theorem not_gammaBoundary_factors_through_sixCameraReturnReadout
    {z : ℂ} (hz : z.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    ¬ ∃ B : ℂ → ℂ, ∀ source : RealifiedCameraComplexification,
      carryGammaPolarizedBoundaryReadout (fun _ => source) z z hz hz =
        B (sixCameraReturnReadout source) := by
  rintro ⟨B, hB⟩
  have hzero : carryGammaComplexState z hz (0 : RealifiedCameraComplexification) = 0 := by
    change (carryGammaSource z hz 0 : WithLp 2 (NaimarkSpace × NaimarkSpace)) = 0
    exact map_zero _
  have h0 := hB 0
  rw [carryGammaPolarizedBoundaryReadout_diagonal_eq_norm_sq] at h0
  have hB0 : (0 : ℂ) = B 0 := by
    rw [hzero] at h0
    simpa [sixCameraReturnReadout] using h0
  have hR := hB (canonicalC3ReturnSourceRemainder z)
  have hread : sixCameraReturnReadout (canonicalC3ReturnSourceRemainder z) = 0 :=
    sixCameraReturnReadout_portRemainder (canonicalCompletedOperatorC3State z)
  rw [hread, ← hB0] at hR
  exact canonicalC3ReturnRemainder_boundary_ne_zero hz hs hR

/-- The exact remaining balance for the named raw sewing: the full three
remainder terms must equal the Wronskian minus the projected Gamma term. -/
theorem canonicalC3RawGammaWronskianDefect_eq_zero_iff_returnBalance
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw = 0 ↔
      (w - conj z) *
        (inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourcePart z))
            (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)) +
         inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
            (carryGammaComplexState w hw (canonicalC3ReturnSourcePart w)) +
         inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
            (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w))) =
        completedGreenWronskian completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z -
        (w - conj z) *
          inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourcePart z))
            (carryGammaComplexState w hw (canonicalC3ReturnSourcePart w)) := by
  rw [canonicalC3RawGammaWronskianDefect_eq_returnFourTerms]
  constructor <;> intro h <;> linear_combination h

end
end CarrySelfAdjointOperator

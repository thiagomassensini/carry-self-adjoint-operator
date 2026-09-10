import CarrySelfAdjointOperator.FiniteCameraRealifiedCauchyInvertibility
import CarrySelfAdjointOperator.SixCameraCauchyMomentCrosswalk
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

open scoped BigOperators ENNReal MeasureTheory RealInnerProductSpace Matrix MatrixOrder ComplexConjugate
open Set MeasureTheory Filter

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 2000000

def imaginarySpectralParameter (eta : ℝ) : ℂ := Complex.I * (eta : ℂ)

@[simp] theorem imaginarySpectralParameter_re (eta : ℝ) :
    (imaginarySpectralParameter eta).re = 0 := by
  simp [imaginarySpectralParameter]

@[simp] theorem imaginarySpectralParameter_im (eta : ℝ) :
    (imaginarySpectralParameter eta).im = eta := by
  simp [imaginarySpectralParameter]

 theorem imaginarySpectralParameter_im_ne_zero {eta : ℝ} (heta : 0 < eta) :
    (imaginarySpectralParameter eta).im ≠ 0 := by
  simp [imaginarySpectralParameter_im, ne_of_gt heta]

/-- The realification complex structure on a finite camera carrier. -/
def finiteCameraComplexStructure
    {ι : Type*} [Fintype ι] :
    FiniteCameraRealification ι →L[ℝ] FiniteCameraRealification ι :=
  realifiedContinuousLinearBlock 0 (ContinuousLinearMap.id ℝ _)

@[simp] theorem finiteCameraComplexStructure_fst
    {ι : Type*} [Fintype ι] (z : FiniteCameraRealification ι) :
    (finiteCameraComplexStructure z).fst = -z.snd := by
  simp [finiteCameraComplexStructure]

@[simp] theorem finiteCameraComplexStructure_snd
    {ι : Type*} [Fintype ι] (z : FiniteCameraRealification ι) :
    (finiteCameraComplexStructure z).snd = z.fst := by
  simp [finiteCameraComplexStructure]

 theorem finiteCameraComplexStructure_sq
    {ι : Type*} [Fintype ι] (z : FiniteCameraRealification ι) :
    finiteCameraComplexStructure (finiteCameraComplexStructure z) = -z := by
  apply (WithLp.ext_iff 2).2
  apply Prod.ext
  · simp
  · simp

/-- A real operator acting diagonally on the two quadratures. -/
def finiteCameraRealifiedDiagonalOperator
    {ι : Type*} [Fintype ι]
    (A : FiniteCameraCoordinates ι →L[ℝ] FiniteCameraCoordinates ι) :
    FiniteCameraRealification ι →L[ℝ] FiniteCameraRealification ι :=
  realifiedContinuousLinearBlock A 0

@[simp] theorem finiteCameraRealifiedDiagonalOperator_fst
    {ι : Type*} [Fintype ι]
    (A : FiniteCameraCoordinates ι →L[ℝ] FiniteCameraCoordinates ι)
    (z : FiniteCameraRealification ι) :
    (finiteCameraRealifiedDiagonalOperator A z).fst = A z.fst := by
  simp [finiteCameraRealifiedDiagonalOperator]

@[simp] theorem finiteCameraRealifiedDiagonalOperator_snd
    {ι : Type*} [Fintype ι]
    (A : FiniteCameraCoordinates ι →L[ℝ] FiniteCameraCoordinates ι)
    (z : FiniteCameraRealification ι) :
    (finiteCameraRealifiedDiagonalOperator A z).snd = A z.snd := by
  simp [finiteCameraRealifiedDiagonalOperator]

 theorem finiteCameraComplexStructure_diagonal_comm
    {ι : Type*} [Fintype ι]
    (A : FiniteCameraCoordinates ι →L[ℝ] FiniteCameraCoordinates ι)
    (z : FiniteCameraRealification ι) :
    finiteCameraComplexStructure (finiteCameraRealifiedDiagonalOperator A z) =
      finiteCameraRealifiedDiagonalOperator A (finiteCameraComplexStructure z) := by
  apply (WithLp.ext_iff 2).2
  apply Prod.ext <;> simp

 theorem tendsto_ofReal_inv_atTop_complex :
    Tendsto (fun eta : ℝ => (eta : ℂ)⁻¹) atTop (nhds 0) := by
  have h := (Complex.continuous_ofReal.continuousAt.tendsto).comp
    (tendsto_inv_atTop_zero (𝕜 := ℝ))
  convert h using 1
  · funext eta
    simp [Function.comp_apply, Complex.ofReal_inv]
  · norm_num

 theorem imaginary_resolvent_inv_tendsto :
    Tendsto (fun eta : ℝ => (Complex.I * (eta : ℂ))⁻¹)
      atTop (nhds 0) := by
  have h := tendsto_ofReal_inv_atTop_complex.const_mul (-Complex.I)
  have h' : Tendsto (fun eta : ℝ => -Complex.I * (eta : ℂ)⁻¹)
      atTop (nhds 0) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with eta heta
  have heta0 : (eta : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt heta)
  field_simp [heta0, Complex.I_ne_zero]
  norm_num [Complex.I_mul_I]

 theorem imaginary_resolvent_ratio_tendsto (y : ℝ) :
    Tendsto
      (fun eta : ℝ => (Complex.I * (eta : ℂ)) /
        (Complex.I * (eta : ℂ) - (y : ℂ)))
      atTop (nhds 1) := by
  have hsmall : Tendsto
      (fun eta : ℝ => (y : ℂ) * (Complex.I * (eta : ℂ))⁻¹)
      atTop (nhds 0) := by
    have h := imaginary_resolvent_inv_tendsto.const_mul (y : ℂ)
    simpa using h
  have hden : Tendsto
      (fun eta : ℝ => 1 - (y : ℂ) * (Complex.I * (eta : ℂ))⁻¹)
      atTop (nhds 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hsmall
  have hrecip : Tendsto
      (fun eta : ℝ =>
        (1 - (y : ℂ) * (Complex.I * (eta : ℂ))⁻¹)⁻¹)
      atTop (nhds 1) := by
    have h := hden.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
    simpa using h
  apply hrecip.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with eta heta
  have heta0 : (eta : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt heta)
  field_simp [heta0, Complex.I_ne_zero]

 theorem imaginary_resolvent_ratio_norm_le {eta y : ℝ} (heta : 0 < eta) :
    ‖(Complex.I * (eta : ℂ)) /
        (Complex.I * (eta : ℂ) - (y : ℂ))‖ ≤ 1 := by
  rw [norm_div]
  have hnum : ‖Complex.I * (eta : ℂ)‖ = eta := by
    rw [norm_mul, Complex.norm_I]
    simp [abs_of_pos heta]
  have hden : ‖Complex.I * (eta : ℂ) - (y : ℂ)‖ ^ 2 = eta ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hden_le : eta ≤ ‖Complex.I * (eta : ℂ) - (y : ℂ)‖ := by
    have hnonneg : 0 ≤ ‖Complex.I * (eta : ℂ) - (y : ℂ)‖ := norm_nonneg _
    nlinarith [sq_nonneg y]
  rw [hnum]
  have hpos : 0 < ‖Complex.I * (eta : ℂ) - (y : ℂ)‖ :=
    lt_of_lt_of_le heta hden_le
  apply (div_le_iff₀ hpos).2
  simpa only [one_mul] using hden_le

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 2000000

/-- The positive integer sequence used for the imaginary high-energy axis. -/
def imaginarySpectralParameterNat (n : ℕ) : ℂ :=
  imaginarySpectralParameter ((n + 1 : ℕ) : ℝ)

@[simp] theorem imaginarySpectralParameterNat_re (n : ℕ) :
    (imaginarySpectralParameterNat n).re = 0 := by
  simp [imaginarySpectralParameterNat]

@[simp] theorem imaginarySpectralParameterNat_im (n : ℕ) :
    (imaginarySpectralParameterNat n).im = (n + 1 : ℕ) := by
  simp [imaginarySpectralParameterNat]

 theorem imaginarySpectralParameterNat_im_ne_zero (n : ℕ) :
    (imaginarySpectralParameterNat n).im ≠ 0 := by
  rw [imaginarySpectralParameterNat_im]
  positivity

/-- The diagonal realified lift of a finite camera matrix. -/
def finiteCameraRealifiedMatrixOperator
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) :
    FiniteCameraRealification ι →L[ℝ] FiniteCameraRealification ι :=
  finiteCameraRealifiedDiagonalOperator
    (LinearMap.toContinuousLinearMap (finiteCameraMatrixMulVec A))

@[simp] theorem finiteCameraRealifiedMatrixOperator_fst
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (z : FiniteCameraRealification ι) :
    (finiteCameraRealifiedMatrixOperator A z).fst = A *ᵥ z.fst := by
  simp [finiteCameraRealifiedMatrixOperator, finiteCameraMatrixMulVec]

@[simp] theorem finiteCameraRealifiedMatrixOperator_snd
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (z : FiniteCameraRealification ι) :
    (finiteCameraRealifiedMatrixOperator A z).snd = A *ᵥ z.snd := by
  simp [finiteCameraRealifiedMatrixOperator, finiteCameraMatrixMulVec]

/-- The three realified six-camera moment operators. -/
def sixCameraRealifiedLogOperator :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  finiteCameraRealifiedMatrixOperator sixCameraLogOperator

def sixCameraRealifiedSecondMoment :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  finiteCameraRealifiedMatrixOperator sixCameraWhitenedSecondMoment

def sixCameraRealifiedVariance :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  finiteCameraRealifiedMatrixOperator sixCameraVariance

@[simp] theorem sixCameraRealifiedLogOperator_fst (z : SixCameraRealification) :
    (sixCameraRealifiedLogOperator z).fst = sixCameraLogOperator *ᵥ z.fst := by
  simp [sixCameraRealifiedLogOperator]

@[simp] theorem sixCameraRealifiedLogOperator_snd (z : SixCameraRealification) :
    (sixCameraRealifiedLogOperator z).snd = sixCameraLogOperator *ᵥ z.snd := by
  simp [sixCameraRealifiedLogOperator]

@[simp] theorem sixCameraRealifiedSecondMoment_fst (z : SixCameraRealification) :
    (sixCameraRealifiedSecondMoment z).fst = sixCameraWhitenedSecondMoment *ᵥ z.fst := by
  simp [sixCameraRealifiedSecondMoment]

@[simp] theorem sixCameraRealifiedSecondMoment_snd (z : SixCameraRealification) :
    (sixCameraRealifiedSecondMoment z).snd = sixCameraWhitenedSecondMoment *ᵥ z.snd := by
  simp [sixCameraRealifiedSecondMoment]

@[simp] theorem sixCameraRealifiedVariance_fst (z : SixCameraRealification) :
    (sixCameraRealifiedVariance z).fst = sixCameraVariance *ᵥ z.fst := by
  simp [sixCameraRealifiedVariance]

@[simp] theorem sixCameraRealifiedVariance_snd (z : SixCameraRealification) :
    (sixCameraRealifiedVariance z).snd = sixCameraVariance *ᵥ z.snd := by
  simp [sixCameraRealifiedVariance]

 theorem finiteCameraComplexStructure_realifiedMatrixOperator_comm
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (z : FiniteCameraRealification ι) :
    finiteCameraComplexStructure (finiteCameraRealifiedMatrixOperator A z) =
      finiteCameraRealifiedMatrixOperator A (finiteCameraComplexStructure z) := by
  exact finiteCameraComplexStructure_diagonal_comm
    (LinearMap.toContinuousLinearMap (finiteCameraMatrixMulVec A)) z

 theorem sixCameraRealifiedLogOperator_complexStructure_comm (z : SixCameraRealification) :
    finiteCameraComplexStructure (sixCameraRealifiedLogOperator z) =
      sixCameraRealifiedLogOperator (finiteCameraComplexStructure z) := by
  exact finiteCameraComplexStructure_realifiedMatrixOperator_comm sixCameraLogOperator z

 theorem sixCameraRealifiedSecondMoment_complexStructure_comm (z : SixCameraRealification) :
    finiteCameraComplexStructure (sixCameraRealifiedSecondMoment z) =
      sixCameraRealifiedSecondMoment (finiteCameraComplexStructure z) := by
  exact finiteCameraComplexStructure_realifiedMatrixOperator_comm
    sixCameraWhitenedSecondMoment z

 theorem sixCameraRealifiedVariance_complexStructure_comm (z : SixCameraRealification) :
    finiteCameraComplexStructure (sixCameraRealifiedVariance z) =
      sixCameraRealifiedVariance (finiteCameraComplexStructure z) := by
  exact finiteCameraComplexStructure_realifiedMatrixOperator_comm sixCameraVariance z

/-- The six-camera Cauchy block along the positive imaginary axis. -/
def sixCameraImaginaryAxisCauchy (n : ℕ) :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  sixCameraRealifiedCauchyBlock (imaginarySpectralParameterNat n)
    (imaginarySpectralParameterNat_im_ne_zero n)

/-- The normalized Cauchy block, with the scalar magnitude removed. -/
def sixCameraImaginaryAxisNormalizedCauchy (n : ℕ) :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  ((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure ∘L
    sixCameraImaginaryAxisCauchy n

/-- An everywhere-defined candidate inverse for the normalized block. -/
def sixCameraImaginaryAxisNormalizedWeyl (n : ℕ) :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  sixCameraIntrinsicWeylBlock (imaginarySpectralParameterNat n)
    (imaginarySpectralParameterNat_im_ne_zero n) ∘L
      (((-((n + 1 : ℕ) : ℝ)⁻¹)) • finiteCameraComplexStructure)

 theorem sixCameraImaginaryAxisNormalizedCauchy_apply (n : ℕ)
    (z : SixCameraRealification) :
    sixCameraImaginaryAxisNormalizedCauchy n z =
      ((n + 1 : ℕ) : ℝ) •
        finiteCameraComplexStructure (sixCameraImaginaryAxisCauchy n z) := by
  simp [sixCameraImaginaryAxisNormalizedCauchy]

 theorem sixCameraImaginaryAxisNormalizedWeyl_apply (n : ℕ)
    (z : SixCameraRealification) :
    sixCameraImaginaryAxisNormalizedWeyl n z =
      sixCameraIntrinsicWeylBlock (imaginarySpectralParameterNat n)
        (imaginarySpectralParameterNat_im_ne_zero n)
        (-((n + 1 : ℕ) : ℝ)⁻¹ • finiteCameraComplexStructure z) := by
  simp [sixCameraImaginaryAxisNormalizedWeyl]

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 2000000

 theorem sixCameraImaginaryAxisNormalizedWeyl_comp_cauchy (n : ℕ)
    (z : SixCameraRealification) :
    sixCameraImaginaryAxisNormalizedWeyl n
      (sixCameraImaginaryAxisNormalizedCauchy n z) = z := by
  simp only [sixCameraImaginaryAxisNormalizedWeyl_apply,
    sixCameraImaginaryAxisNormalizedCauchy_apply,
    map_smul]
  have hsq := finiteCameraComplexStructure_sq
    (sixCameraImaginaryAxisCauchy n z)
  rw [hsq, map_neg]
  have hw : sixCameraIntrinsicWeylBlock (imaginarySpectralParameterNat n)
      (imaginarySpectralParameterNat_im_ne_zero n)
      (sixCameraImaginaryAxisCauchy n z) = z := by
    simpa [sixCameraImaginaryAxisCauchy] using
      (sixCameraIntrinsicWeylBlock_comp_cauchy
        (lambda := imaginarySpectralParameterNat n)
        (imaginarySpectralParameterNat_im_ne_zero n)
        z)
  rw [hw]
  rw [smul_smul]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp
  simp

 theorem sixCameraImaginaryAxisNormalizedCauchy_comp_weyl (n : ℕ)
    (z : SixCameraRealification) :
    sixCameraImaginaryAxisNormalizedCauchy n
      (sixCameraImaginaryAxisNormalizedWeyl n z) = z := by
  simp only [sixCameraImaginaryAxisNormalizedCauchy_apply,
    sixCameraImaginaryAxisNormalizedWeyl_apply,
    map_smul]
  have hw : sixCameraImaginaryAxisCauchy n
      (sixCameraIntrinsicWeylBlock (imaginarySpectralParameterNat n)
        (imaginarySpectralParameterNat_im_ne_zero n)
        (finiteCameraComplexStructure z)) =
      finiteCameraComplexStructure z := by
    simpa [sixCameraImaginaryAxisCauchy] using
      (sixCameraRealifiedCauchyBlock_comp_intrinsicWeyl
        (lambda := imaginarySpectralParameterNat n)
        (imaginarySpectralParameterNat_im_ne_zero n)
        (finiteCameraComplexStructure z))
  rw [hw]
  have hsq := finiteCameraComplexStructure_sq z
  rw [hsq]
  rw [smul_smul]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp
  simp

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

 theorem inverse_one_add_exact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N W : E →L[ℝ] E)
    (hWN : ∀ z, N (W z) = z) (z : E) :
    W z = z - (N - ContinuousLinearMap.id ℝ E) z +
      (N - ContinuousLinearMap.id ℝ E)
        ((N - ContinuousLinearMap.id ℝ E) (W z)) := by
  let K : E →L[ℝ] E := N - ContinuousLinearMap.id ℝ E
  have h := hWN z
  have hrewrite : N = ContinuousLinearMap.id ℝ E + K := by
    ext x
    simp [K]
  rw [hrewrite, add_apply, ContinuousLinearMap.id_apply] at h
  have hK := congrArg K h
  rw [map_add] at hK
  change W z = z - K z + K (K (W z))
  change W z + K (W z) = z at h
  have hKcomm : K (K (W z)) + K (W z) = K z := by
    simpa [add_comm] using hK
  have hK1 : K (K (W z)) = K z - K (W z) :=
    eq_sub_of_add_eq hKcomm
  rw [hK1]
  have hfinal : W z = z - K (W z) := (eq_sub_iff_add_eq).2 h
  calc
    W z = z - K (W z) := hfinal
    _ = z - K z + (K z - K (W z)) := by abel

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

 theorem sixCameraImaginaryAxisNormalizedWeyl_comp_cauchy_clm (n : ℕ) :
    sixCameraImaginaryAxisNormalizedWeyl n ∘L
        sixCameraImaginaryAxisNormalizedCauchy n =
      ContinuousLinearMap.id ℝ SixCameraRealification := by
  apply ContinuousLinearMap.ext
  intro z
  simpa [ContinuousLinearMap.comp_apply] using
    sixCameraImaginaryAxisNormalizedWeyl_comp_cauchy n z

 theorem sixCameraImaginaryAxisNormalizedCauchy_comp_weyl_clm (n : ℕ) :
    sixCameraImaginaryAxisNormalizedCauchy n ∘L
        sixCameraImaginaryAxisNormalizedWeyl n =
      ContinuousLinearMap.id ℝ SixCameraRealification := by
  apply ContinuousLinearMap.ext
  intro z
  simpa [ContinuousLinearMap.comp_apply] using
    sixCameraImaginaryAxisNormalizedCauchy_comp_weyl n z

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

 theorem scalar_imaginary_axis_resolvent_third_order (n : ℕ) (y : ℝ) :
    (imaginarySpectralParameterNat n - (y : ℂ))⁻¹ =
      (imaginarySpectralParameterNat n)⁻¹ +
        (imaginarySpectralParameterNat n)⁻¹ *
          (imaginarySpectralParameterNat n)⁻¹ * (y : ℂ) +
        (imaginarySpectralParameterNat n)⁻¹ *
          (imaginarySpectralParameterNat n)⁻¹ * (y : ℂ) ^ 2 *
            (imaginarySpectralParameterNat n - (y : ℂ))⁻¹ := by
  exact scalar_resolvent_third_order_of_offReal
    (lambda := imaginarySpectralParameterNat n) (y := y)
    (imaginarySpectralParameterNat_im_ne_zero n)

 theorem imaginary_resolvent_ratio_tendsto_nat (y : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (Complex.I * ((n + 1 : ℕ) : ℂ)) /
          (Complex.I * ((n + 1 : ℕ) : ℂ) - (y : ℂ)))
      atTop (nhds 1) := by
  have h := imaginary_resolvent_ratio_tendsto y
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hcomp := h.comp hcast
  convert hcomp using 1
  · funext n
    simp [Function.comp_apply, Nat.cast_add, Nat.cast_one]


 theorem imaginary_resolvent_ratio_norm_le_nat (n : ℕ) (y : ℝ) :
    ‖(Complex.I * ((n + 1 : ℕ) : ℂ)) /
        (Complex.I * ((n + 1 : ℕ) : ℂ) - (y : ℂ))‖ ≤ 1 := by
  apply imaginary_resolvent_ratio_norm_le
  positivity

/-- The intrinsic Weyl is recovered from the normalized inverse by restoring
    the imaginary-axis scale and the realified complex structure. -/
theorem sixCameraIntrinsicWeylBlock_eq_normalizedWeyl_comp_scale
    (n : ℕ) (z : SixCameraRealification) :
    sixCameraIntrinsicWeylBlock (imaginarySpectralParameterNat n)
        (imaginarySpectralParameterNat_im_ne_zero n) z =
      sixCameraImaginaryAxisNormalizedWeyl n
        (((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure z) := by
  rw [sixCameraImaginaryAxisNormalizedWeyl_apply]
  simp only [map_smul, smul_smul]
  rw [finiteCameraComplexStructure_sq]
  have hη : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hprod : -((n + 1 : ℕ) : ℝ)⁻¹ * ((n + 1 : ℕ) : ℝ) = (-1 : ℝ) := by
    exact (neg_mul (a := ((n + 1 : ℕ) : ℝ)⁻¹)
      (b := ((n + 1 : ℕ) : ℝ))).trans
      (congrArg Neg.neg (inv_mul_cancel₀ hη))
  rw [hprod]
  simp


/-- Exact vector form of the second-order inverse identity.  This is the
finite-dimensional algebraic reduction used by any subsequent high-energy
limit proof. -/
theorem finiteCameraIntrinsicWeyl_inverse_second_order_exact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N W : E →L[ℝ] E)
    (hWN : ∀ z, N (W z) = z) (z : E) :
    W z = z - (N - ContinuousLinearMap.id ℝ E) z +
      (N - ContinuousLinearMap.id ℝ E)
        ((N - ContinuousLinearMap.id ℝ E) (W z)) :=
  inverse_one_add_exact N W hWN z

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-- The residual left after removing the identity and the first two
imaginary-axis moment terms from a normalized finite Cauchy block. -/
def finiteCameraNormalizedSecondOrderRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N A B : E →L[ℝ] E) (eta : ℝ) : E →L[ℝ] E :=
  eta ^ 2 •
    (N - ContinuousLinearMap.id ℝ E + eta⁻¹ • A + (eta⁻¹) ^ 2 • B)

 theorem finiteCameraNormalizedSecondOrderRemainder_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N A B : E →L[ℝ] E} {eta : ℝ} (heta : eta ≠ 0) :
    N = ContinuousLinearMap.id ℝ E - eta⁻¹ • A - eta⁻¹ ^ 2 • B +
      eta⁻¹ ^ 2 • finiteCameraNormalizedSecondOrderRemainder N A B eta := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [finiteCameraNormalizedSecondOrderRemainder, smul_apply,
    add_apply, sub_apply, ContinuousLinearMap.id_apply]
  rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  simp only [smul_add, smul_smul]
  have hpow : (eta⁻¹ ^ 2) * eta ^ 2 = (1 : ℝ) := by
    field_simp [heta]
  rw [hpow]
  have hpow2 : (eta⁻¹ ^ 2) * eta = eta⁻¹ := by
    field_simp [heta]
  have hpow3 : (eta⁻¹ ^ 2) * (eta ^ 2 * eta⁻¹) = eta⁻¹ := by
    field_simp [heta]
  rw [hpow3]
  simp only [one_smul, one_mul]
  module

/-- The concrete second-order residual for the six-camera normalized Cauchy
family.  It is a definition of the exact residual, so no asymptotic claim is
hidden in the notation. -/
def sixCameraImaginaryAxisNormalizedSecondOrderRemainder (n : ℕ) :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  finiteCameraNormalizedSecondOrderRemainder
    (sixCameraImaginaryAxisNormalizedCauchy n)
    (finiteCameraComplexStructure ∘L sixCameraRealifiedLogOperator)
    sixCameraRealifiedSecondMoment
    ((n + 1 : ℕ) : ℝ)

 theorem sixCameraImaginaryAxisNormalizedCauchy_second_order_decomposition
    (n : ℕ) :
    sixCameraImaginaryAxisNormalizedCauchy n =
      ContinuousLinearMap.id ℝ SixCameraRealification -
          (((n + 1 : ℕ) : ℝ)⁻¹) •
            (finiteCameraComplexStructure ∘L sixCameraRealifiedLogOperator) -
          (((n + 1 : ℕ) : ℝ)⁻¹) ^ 2 • sixCameraRealifiedSecondMoment +
        (((n + 1 : ℕ) : ℝ)⁻¹) ^ 2 •
          sixCameraImaginaryAxisNormalizedSecondOrderRemainder n := by
  exact finiteCameraNormalizedSecondOrderRemainder_decomposition
    (by positivity)

 theorem sixCameraIntrinsicWeyl_first_return_defect_eq_normalized_inverse
    (n : ℕ) (z : SixCameraRealification) :
    ((n + 1 : ℕ) : ℝ) •
        (sixCameraIntrinsicWeylBlock (imaginarySpectralParameterNat n)
          (imaginarySpectralParameterNat_im_ne_zero n) z -
          ((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure z +
          sixCameraRealifiedLogOperator z) =
      ((n + 1 : ℕ) : ℝ) •
        (sixCameraImaginaryAxisNormalizedWeyl n
          (((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure z) -
          ((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure z +
          sixCameraRealifiedLogOperator z) := by
  rw [sixCameraIntrinsicWeylBlock_eq_normalizedWeyl_comp_scale]

end
end CarrySelfAdjointOperator


namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

/-- After scaling, the exact third-order scalar remainder is a second moment
factor times the bounded resolvent ratio. -/
theorem scalar_imaginary_axis_resolvent_scaled_remainder
    (n : ℕ) (y : ℝ) :
    (imaginarySpectralParameterNat n) ^ 3 *
        ((imaginarySpectralParameterNat n - (y : ℂ))⁻¹ -
          (imaginarySpectralParameterNat n)⁻¹ -
          (imaginarySpectralParameterNat n)⁻¹ *
            (imaginarySpectralParameterNat n)⁻¹ * (y : ℂ)) =
      (y : ℂ) ^ 2 *
        (imaginarySpectralParameterNat n) /
          (imaginarySpectralParameterNat n - (y : ℂ)) := by
  rw [scalar_imaginary_axis_resolvent_third_order]
  have hη : imaginarySpectralParameterNat n ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    linarith
  field_simp [hη]
  ring

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Finite
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-- The first-order realified moment operator appearing in the normalized
imaginary-axis Cauchy block. -/
def sixCameraRealifiedFirstOrder :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  finiteCameraComplexStructure ∘L sixCameraRealifiedLogOperator

 theorem sixCameraRealifiedFirstOrder_apply_complexStructure (z : SixCameraRealification) :
    sixCameraRealifiedFirstOrder (finiteCameraComplexStructure z) =
      -sixCameraRealifiedLogOperator z := by
  rw [sixCameraRealifiedFirstOrder, ContinuousLinearMap.comp_apply,
    sixCameraRealifiedLogOperator_complexStructure_comm,
    finiteCameraComplexStructure_sq]
  simp only [map_neg]

/-- The second-order inverse residual on the normalized axis. -/
def sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder (n : ℕ) :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  finiteCameraNormalizedSecondOrderRemainder
    (sixCameraImaginaryAxisNormalizedWeyl n)
    (-sixCameraRealifiedFirstOrder)
    (-(sixCameraRealifiedSecondMoment +
      sixCameraRealifiedFirstOrder ∘L sixCameraRealifiedFirstOrder))
    ((n + 1 : ℕ) : ℝ)

theorem sixCameraRealifiedSecondMoment_sub_logSquare
    (z : SixCameraRealification) :
    sixCameraRealifiedSecondMoment z -
        sixCameraRealifiedLogOperator
          (sixCameraRealifiedLogOperator z) =
      sixCameraRealifiedVariance z := by
  apply (WithLp.ext_iff 2).2
  apply Prod.ext
  · change (sixCameraRealifiedSecondMoment z).fst -
      (sixCameraRealifiedLogOperator
        (sixCameraRealifiedLogOperator z)).fst =
      (sixCameraRealifiedVariance z).fst
    unfold sixCameraRealifiedSecondMoment sixCameraRealifiedLogOperator
      sixCameraRealifiedVariance
    simp [finiteCameraRealifiedMatrixOperator,
      finiteCameraRealifiedDiagonalOperator, finiteCameraMatrixMulVec]
    rw [← WithLp.toLp_sub, ← Matrix.sub_mulVec]
    rfl
  · change (sixCameraRealifiedSecondMoment z).snd -
      (sixCameraRealifiedLogOperator
        (sixCameraRealifiedLogOperator z)).snd =
      (sixCameraRealifiedVariance z).snd
    unfold sixCameraRealifiedSecondMoment sixCameraRealifiedLogOperator
      sixCameraRealifiedVariance
    simp [finiteCameraRealifiedMatrixOperator,
      finiteCameraRealifiedDiagonalOperator, finiteCameraMatrixMulVec]
    rw [← WithLp.toLp_sub, ← Matrix.sub_mulVec]
    rfl

/-- The second-order coefficient tested in the complex-structure
    quadrature is the complex structure applied to the real variance block. -/
theorem sixCameraRealifiedSecondOrderCoefficient_apply_complexStructure
    (z : SixCameraRealification) :
    (sixCameraRealifiedSecondMoment +
      sixCameraRealifiedFirstOrder ∘L sixCameraRealifiedFirstOrder)
        (finiteCameraComplexStructure z) =
      finiteCameraComplexStructure (sixCameraRealifiedVariance z) := by
  change sixCameraRealifiedSecondMoment (finiteCameraComplexStructure z) +
      sixCameraRealifiedFirstOrder
        (sixCameraRealifiedFirstOrder (finiteCameraComplexStructure z)) =
    finiteCameraComplexStructure (sixCameraRealifiedVariance z)
  rw [sixCameraRealifiedFirstOrder_apply_complexStructure]
  simp only [sixCameraRealifiedFirstOrder, ContinuousLinearMap.comp_apply,
    map_neg]
  rw [← sixCameraRealifiedSecondMoment_complexStructure_comm]
  rw [← sub_eq_add_neg, ← map_sub,
    sixCameraRealifiedSecondMoment_sub_logSquare]

/-- The exact scaled first-return residual.  Its convergence to the
    second-order coefficient is the only analytic step not supplied by the
    current pin. -/
theorem finiteCameraScaledSecondOrder_cancel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (hη : η ≠ 0) (a b c d : E) :
    η • (η • (a + η⁻¹ • (-b) + η⁻¹ ^ 2 • c + η⁻¹ ^ 2 • d) -
        η • a + b) = c + d := by
  simp only [smul_add, smul_neg, smul_smul, sub_eq_add_neg]
  simp [hη, pow_two]
  module

def sixCameraIntrinsicWeylFirstReturnResidual (n : ℕ) :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  ((n + 1 : ℕ) : ℝ) •
    (sixCameraImaginaryAxisNormalizedWeyl n ∘L
        (((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure) -
      ((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure +
      sixCameraRealifiedLogOperator)

/-- Exact second-order decomposition of the normalized intrinsic inverse.
    No limit assertion is bundled: the final summand is the named remainder. -/
theorem sixCameraImaginaryAxisNormalizedWeyl_second_order_decomposition
    (n : ℕ) :
    sixCameraImaginaryAxisNormalizedWeyl n =
      ContinuousLinearMap.id ℝ SixCameraRealification +
          (((n + 1 : ℕ) : ℝ)⁻¹) • sixCameraRealifiedFirstOrder +
          (((n + 1 : ℕ) : ℝ)⁻¹) ^ 2 •
            (sixCameraRealifiedSecondMoment +
              sixCameraRealifiedFirstOrder ∘L sixCameraRealifiedFirstOrder) +
          (((n + 1 : ℕ) : ℝ)⁻¹) ^ 2 •
            sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder n := by
  have h :=
    finiteCameraNormalizedSecondOrderRemainder_decomposition
      (N := sixCameraImaginaryAxisNormalizedWeyl n)
      (A := -sixCameraRealifiedFirstOrder)
      (B := -(sixCameraRealifiedSecondMoment +
        sixCameraRealifiedFirstOrder ∘L sixCameraRealifiedFirstOrder))
      (eta := ((n + 1 : ℕ) : ℝ)) (by positivity)
  rw [h]
  simp only [sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder,
    sub_eq_add_neg, neg_neg, smul_neg, smul_add, inv_pow]

/-- The exact first-return residual splits into the second-order
    coefficient and the named inverse remainder. -/
theorem sixCameraIntrinsicWeylFirstReturnResidual_eq_coefficient_add_remainder
    (n : ℕ) (z : SixCameraRealification) :
    sixCameraIntrinsicWeylFirstReturnResidual n z =
      (sixCameraRealifiedSecondMoment +
        sixCameraRealifiedFirstOrder ∘L sixCameraRealifiedFirstOrder)
          (finiteCameraComplexStructure z) +
        sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder n
          (finiteCameraComplexStructure z) := by
  rw [sixCameraIntrinsicWeylFirstReturnResidual,
    sixCameraImaginaryAxisNormalizedWeyl_second_order_decomposition]
  simp only [smul_apply, add_apply, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_smul]
  have hη : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [sixCameraRealifiedFirstOrder_apply_complexStructure]
  exact finiteCameraScaledSecondOrder_cancel
    (((n + 1 : ℕ) : ℝ)) hη
    (finiteCameraComplexStructure z)
    (sixCameraRealifiedLogOperator z)
    (sixCameraRealifiedSecondMoment (finiteCameraComplexStructure z) +
      sixCameraRealifiedFirstOrder (-sixCameraRealifiedLogOperator z))
    (sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder n
      (finiteCameraComplexStructure z))

theorem sixCameraIntrinsicWeylFirstReturnResidual_eq_variance_add_remainder
    (n : ℕ) (z : SixCameraRealification) :
    sixCameraIntrinsicWeylFirstReturnResidual n z =
      finiteCameraComplexStructure (sixCameraRealifiedVariance z) +
        sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder n
          (finiteCameraComplexStructure z) := by
  rw [sixCameraIntrinsicWeylFirstReturnResidual_eq_coefficient_add_remainder,
    sixCameraRealifiedSecondOrderCoefficient_apply_complexStructure]

/-- The intrinsic first-return expression is exactly the residual obtained
    from the normalized inverse after restoring the imaginary-axis scale. -/
theorem sixCameraIntrinsicWeyl_first_return_eq_residual
    (n : ℕ) (z : SixCameraRealification) :
    ((n + 1 : ℕ) : ℝ) •
        (sixCameraIntrinsicWeylBlock (imaginarySpectralParameterNat n)
          (imaginarySpectralParameterNat_im_ne_zero n) z -
          ((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure z +
          sixCameraRealifiedLogOperator z) =
      sixCameraIntrinsicWeylFirstReturnResidual n z := by
  rw [sixCameraIntrinsicWeylFirstReturnResidual,
    sixCameraIntrinsicWeylBlock_eq_normalizedWeyl_comp_scale]
  simp only [smul_apply, add_apply, sub_apply, ContinuousLinearMap.comp_apply]

theorem sixCameraIntrinsicWeyl_first_return_tendsto_of_inverse_remainder
    (z : SixCameraRealification)
    (h :
      Tendsto
        (fun n : ℕ =>
          sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder n
            (finiteCameraComplexStructure z))
        atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) •
          (sixCameraIntrinsicWeylBlock (imaginarySpectralParameterNat n)
            (imaginarySpectralParameterNat_im_ne_zero n) z -
            ((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure z +
            sixCameraRealifiedLogOperator z))
      atTop (nhds (finiteCameraComplexStructure (sixCameraRealifiedVariance z))) := by
  have hsum :
      Tendsto
        (fun n : ℕ =>
          finiteCameraComplexStructure (sixCameraRealifiedVariance z) +
            sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder n
              (finiteCameraComplexStructure z))
        atTop (nhds (finiteCameraComplexStructure (sixCameraRealifiedVariance z))) :=
    by
      simpa using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ =>
            finiteCameraComplexStructure (sixCameraRealifiedVariance z))
            atTop (nhds (finiteCameraComplexStructure (sixCameraRealifiedVariance z)))).add h)
  refine hsum.congr' ?_
  filter_upwards [] with n
  rw [← sixCameraIntrinsicWeylFirstReturnResidual_eq_variance_add_remainder n z]
  exact (sixCameraIntrinsicWeyl_first_return_eq_residual n z).symm

theorem sixCameraIntrinsicWeyl_first_return_tendsto_of_residual
    (z w : SixCameraRealification)
    (h :
      Tendsto (fun n : ℕ => sixCameraIntrinsicWeylFirstReturnResidual n z)
        atTop (nhds w)) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) •
          (sixCameraIntrinsicWeylBlock (imaginarySpectralParameterNat n)
            (imaginarySpectralParameterNat_im_ne_zero n) z -
            ((n + 1 : ℕ) : ℝ) • finiteCameraComplexStructure z +
            sixCameraRealifiedLogOperator z))
      atTop (nhds w) := by
  refine h.congr' ?_
  filter_upwards [] with n
  exact (sixCameraIntrinsicWeyl_first_return_eq_residual n z).symm

end
end CarrySelfAdjointOperator

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

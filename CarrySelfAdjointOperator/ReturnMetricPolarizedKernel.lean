import NativeCarrySpectralWeyl.Finite.ReturnMetric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Polarized kernels in the endpoint return metric

The finite Poisson identities `P E = D` and `Eᴴ E + Dᴴ D = I`
already imply `Eᴴ (I + Pᴴ P) E = I` upstream.  This module keeps
both probe legs independent, proves positivity of every finite section,
and derives the division-free resolvent identity with its exact sign.

The camera map and the colligation are fixed across the two parameters.
No identification of the compressed resolvent with the completed-native
logarithmic response is assumed or asserted.
-/

open scoped Matrix ComplexOrder

namespace CarrySelfAdjointOperator.ReturnMetric

open NativeCarrySpectralWeyl.Finite

noncomputable section

variable {spectral endpoint bulk output : Type*}
variable [Fintype spectral] [Fintype endpoint] [Fintype bulk]
variable [DecidableEq spectral] [DecidableEq endpoint]

/-- The two probe legs may use different matrices. -/
def polarizedCovariance (camera : Matrix output spectral ℂ)
    (left right : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ) : Matrix output output ℂ :=
  sourceProbe camera left endpointMap * returnMetric poisson *
    (sourceProbe camera right endpointMap)ᴴ

/-- Exact return-metric cancellation with independent left and right legs.
Neither leg needs to be a resolvent for this algebraic statement. -/
theorem polarizedCovariance_eq_direct
    (camera : Matrix output spectral ℂ)
    (left right : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    polarizedCovariance camera left right endpointMap poisson =
      camera * left * rightᴴ * cameraᴴ := by
  have hmetric := endpointMap_conjTranspose_mul_returnMetric_mul_endpointMap
    endpointMap bulkMap poisson hpoisson hisometry
  simp only [polarizedCovariance, sourceProbe, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    (camera * left * endpointMapᴴ) * returnMetric poisson *
        (endpointMap * (rightᴴ * cameraᴴ)) =
      camera * left * (endpointMapᴴ * returnMetric poisson * endpointMap) *
        rightᴴ * cameraᴴ := by simp only [Matrix.mul_assoc]
    _ = camera * left * rightᴴ * cameraᴴ := by rw [hmetric]; simp

/-- Both independent legs retain their common Gram factorization. -/
theorem polarizedCovariance_eq_factorization
    (camera : Matrix output spectral ℂ)
    (left right : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    polarizedCovariance camera left right endpointMap poisson =
      (camera * left) * (camera * right)ᴴ := by
  rw [polarizedCovariance_eq_direct camera left right
    endpointMap bulkMap poisson hpoisson hisometry]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Positivity includes every cross term between finitely many parameters
and output coordinates, rather than only the one-parameter diagonal. -/
theorem polarizedCovariance_finiteSection_posSemidef
    {index : Type*} [Finite index] [Finite output]
    (camera : Matrix output spectral ℂ)
    (leg : index → Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    (Matrix.of fun p q : index × output =>
      polarizedCovariance camera (leg p.1) (leg q.1)
        endpointMap poisson p.2 q.2).PosSemidef := by
  let feature : Matrix (index × output) spectral ℂ :=
    fun p k => (camera * leg p.1) p.2 k
  have hfactor :
      (Matrix.of fun p q : index × output =>
        polarizedCovariance camera (leg p.1) (leg q.1)
          endpointMap poisson p.2 q.2) = feature * featureᴴ := by
    ext p q
    change polarizedCovariance camera (leg p.1) (leg q.1)
      endpointMap poisson p.2 q.2 = _
    rw [polarizedCovariance_eq_factorization camera (leg p.1) (leg q.1)
      endpointMap bulkMap poisson hpoisson hisometry]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, feature]
  rw [hfactor]
  exact Matrix.posSemidef_self_mul_conjTranspose feature

/-- In particular, the return-metric diagonal is positive semidefinite. -/
theorem polarizedCovariance_self_posSemidef [Finite output]
    (camera : Matrix output spectral ℂ)
    (leg : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    (polarizedCovariance camera leg leg endpointMap poisson).PosSemidef := by
  rw [polarizedCovariance_eq_factorization camera leg leg
    endpointMap bulkMap poisson hpoisson hisometry]
  exact Matrix.posSemidef_self_mul_conjTranspose (camera * leg)

omit [Fintype endpoint] [Fintype bulk] [DecidableEq endpoint] in
/-- Division-free two-resolvent identity.  The two explicit left-inverse
identities and Hermitian symmetry suffice; no matrix inverse is totalized. -/
theorem resolvent_sub_adjoint_eq_separation_smul
    (operator left right : Matrix spectral spectral ℂ) (z w : ℂ)
    (hoperator : operator.IsHermitian)
    (hleft : left * (z • (1 : Matrix spectral spectral ℂ) - operator) = 1)
    (hright : right * (w • (1 : Matrix spectral spectral ℂ) - operator) = 1) :
    left - rightᴴ = (star w - z) • (left * rightᴴ) := by
  have hrightAdjoint :
      (star w • (1 : Matrix spectral spectral ℂ) - operator) * rightᴴ = 1 := by
    have h := congrArg Matrix.conjTranspose hright
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hoperator.eq] using h
  have hseparation :
      (star w • (1 : Matrix spectral spectral ℂ) - operator) -
        (z • (1 : Matrix spectral spectral ℂ) - operator) =
          (star w - z) • (1 : Matrix spectral spectral ℂ) := by
    simp only [sub_smul]
    abel
  calc
    left - rightᴴ =
        left * ((star w • (1 : Matrix spectral spectral ℂ) - operator) * rightᴴ) -
          (left * (z • (1 : Matrix spectral spectral ℂ) - operator)) * rightᴴ := by
            rw [hrightAdjoint, hleft]
            simp
    _ = left * ((star w • (1 : Matrix spectral spectral ℂ) - operator) -
        (z • (1 : Matrix spectral spectral ℂ) - operator)) * rightᴴ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = (star w - z) • (left * rightᴴ) := by
      rw [hseparation]
      simp

/-- The compressed readout uses the same fixed camera in both legs. -/
def compressedReadout (camera : Matrix output spectral ℂ)
    (leg : Matrix spectral spectral ℂ) : Matrix output output ℂ :=
  camera * leg * cameraᴴ

/-- The exact polarized kernel is the divided-difference numerator, with
separation `conj w - z`.  This statement also applies at zero separation. -/
theorem compressedReadout_sub_adjoint_eq_separation_smul_covariance
    (camera : Matrix output spectral ℂ)
    (operator left right : Matrix spectral spectral ℂ) (z w : ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1)
    (hoperator : operator.IsHermitian)
    (hleft : left * (z • (1 : Matrix spectral spectral ℂ) - operator) = 1)
    (hright : right * (w • (1 : Matrix spectral spectral ℂ) - operator) = 1) :
    compressedReadout camera left - (compressedReadout camera right)ᴴ =
      (star w - z) • polarizedCovariance camera left right endpointMap poisson := by
  rw [polarizedCovariance_eq_direct camera left right
    endpointMap bulkMap poisson hpoisson hisometry]
  have hresolvent := resolvent_sub_adjoint_eq_separation_smul
    operator left right z w hoperator hleft hright
  calc
    compressedReadout camera left - (compressedReadout camera right)ᴴ =
        camera * (left - rightᴴ) * cameraᴴ := by
          simp only [compressedReadout, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
            Matrix.sub_mul, Matrix.mul_assoc]
    _ = (star w - z) • (camera * left * rightᴴ * cameraᴴ) := by
      rw [hresolvent]
      simp [Matrix.mul_assoc]

/-- Away from zero separation, division is now justified by an explicit
nonvanishing hypothesis. -/
theorem polarizedCovariance_eq_inv_separation_smul_readoutDifference
    (camera : Matrix output spectral ℂ)
    (operator left right : Matrix spectral spectral ℂ) (z w : ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1)
    (hoperator : operator.IsHermitian)
    (hleft : left * (z • (1 : Matrix spectral spectral ℂ) - operator) = 1)
    (hright : right * (w • (1 : Matrix spectral spectral ℂ) - operator) = 1)
    (hseparation : star w - z ≠ 0) :
    polarizedCovariance camera left right endpointMap poisson =
      (star w - z)⁻¹ •
        (compressedReadout camera left - (compressedReadout camera right)ᴴ) := by
  rw [compressedReadout_sub_adjoint_eq_separation_smul_covariance
    camera operator left right z w endpointMap bulkMap poisson
    hpoisson hisometry hoperator hleft hright]
  rw [smul_smul, inv_mul_cancel₀ hseparation, one_smul]

/-- On a single non-real parameter, the sign is anti-Herglotz:
`-Im(B(z)) = Im(z) K(z,z)`, written as a matrix identity. -/
theorem negativeImaginaryReadout_eq_im_smul_covariance
    (camera : Matrix output spectral ℂ)
    (operator leg : Matrix spectral spectral ℂ) (z : ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1)
    (hoperator : operator.IsHermitian)
    (hleg : leg * (z • (1 : Matrix spectral spectral ℂ) - operator) = 1) :
    (Complex.I / 2) •
        (compressedReadout camera leg - (compressedReadout camera leg)ᴴ) =
      (z.im : ℂ) • polarizedCovariance camera leg leg endpointMap poisson := by
  rw [compressedReadout_sub_adjoint_eq_separation_smul_covariance
    camera operator leg leg z z endpointMap bulkMap poisson
    hpoisson hisometry hoperator hleg hleg, smul_smul]
  have hfactor : Complex.I / 2 * (star z - z) = (z.im : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [hfactor]

/-- The negative imaginary part of the compressed readout is positive
semidefinite in the upper half-plane, with no native scalar identification. -/
theorem negativeImaginaryReadout_posSemidef [Finite output]
    (camera : Matrix output spectral ℂ)
    (operator leg : Matrix spectral spectral ℂ) (z : ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1)
    (hoperator : operator.IsHermitian)
    (hleg : leg * (z • (1 : Matrix spectral spectral ℂ) - operator) = 1)
    (him : 0 ≤ z.im) :
    ((Complex.I / 2) •
      (compressedReadout camera leg - (compressedReadout camera leg)ᴴ)).PosSemidef := by
  rw [negativeImaginaryReadout_eq_im_smul_covariance camera operator leg z
    endpointMap bulkMap poisson hpoisson hisometry hoperator hleg]
  exact (polarizedCovariance_self_posSemidef camera leg endpointMap bulkMap
    poisson hpoisson hisometry).smul (by exact_mod_cast him : (0 : ℂ) ≤ (z.im : ℂ))

end

end CarrySelfAdjointOperator.ReturnMetric

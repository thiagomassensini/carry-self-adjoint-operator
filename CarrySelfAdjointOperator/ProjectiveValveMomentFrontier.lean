import CarrySelfAdjointOperator.ProjectiveValveNativeIncidence
import CarrySelfAdjointOperator.CompletedNativeCausalCoefficientMomentGate

/-!
# Exact moment obligations for the projective incidence route

A faithful projective transport preserves linear relations. Its Hilbert metric
must additionally satisfy the native response boundary coefficients and the
polarized shift identity. These two obligations are necessary and sufficient
for the full coefficient equation. The literal C3 incidence realization fails
the shift identity already at total degree two.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- The polarized coefficient equation splits exactly into its boundary data
and the interior shift identity. Neither condition asserts positivity. -/
theorem polarizedGreenCoefficientEquation_iff_boundary_transport
    (moments : ℕ → ℝ) (coeff : ℕ → ℕ → ℂ) :
    IsPolarizedGreenCoefficientEquation moments coeff ↔
      (∀ p, coeff p 0 = oddMomentResponseCoefficient moments (p + 1)) ∧
      (∀ p q, coeff p (q + 1) = coeff (p + 1) q) := by
  constructor
  · intro h
    exact ⟨polarizedGreenCoefficient_boundary h,
      polarizedGreenCoefficient_transport h⟩
  · rintro ⟨hboundary, htransport⟩
    have hvalue (p q : ℕ) :
        coeff p q = oddMomentResponseCoefficient moments (p + q + 1) := by
      induction q generalizing p with
      | zero => simpa using hboundary p
      | succ q ih =>
          rw [htransport, ih]
          congr 2
          omega
    have heq : coeff = polarizedGreenMomentCoefficient moments := by
      funext p q
      rw [hvalue]
      rfl
    rw [heq]
    exact polarizedGreenMomentCoefficient_coefficientEquation moments

namespace ProjectiveValve

open CPFormal.Analytic.Cp FiniteNativeCarryOperator.Camera
open scoped InnerProductSpace lp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The native bracket family after a real-linear realization of its
projective finite-support core. -/
def projectiveIncidenceRawJet
    (T : LinearMap.range nativeIncidenceProjectiveMap →ₗ[ℝ] E)
    (base radius n : ℕ) : E :=
  T (nativeIncidenceProjectiveEquivRange (cameraBracketIncidence base radius n))

/-- Actual polarized Hilbert coefficients of the chosen realization. -/
def projectiveIncidenceCoefficient
    (T : LinearMap.range nativeIncidenceProjectiveMap →ₗ[ℝ] E)
    (base radius p q : ℕ) : ℂ :=
  inner ℂ (projectiveIncidenceRawJet T base radius p)
    (projectiveIncidenceRawJet T base radius q)

/-- The exact remaining moment equation for a specified projective
realization. A faithful linear map alone does not supply this proposition. -/
def ProjectiveIncidenceMomentEquation
    (moments : ℕ → ℝ)
    (T : LinearMap.range nativeIncidenceProjectiveMap →ₗ[ℝ] E)
    (base radius : ℕ) : Prop :=
  IsPolarizedGreenCoefficientEquation moments
    (projectiveIncidenceCoefficient T base radius)

/-- Two explicit obligations for the actual Hilbert coefficients: identify
the first column with the native response, and prove shift symmetry. -/
theorem projectiveIncidenceMomentEquation_iff_boundary_transport
    (moments : ℕ → ℝ)
    (T : LinearMap.range nativeIncidenceProjectiveMap →ₗ[ℝ] E)
    (base radius : ℕ) :
    ProjectiveIncidenceMomentEquation moments T base radius ↔
      (∀ p, projectiveIncidenceCoefficient T base radius p 0 =
        oddMomentResponseCoefficient moments (p + 1)) ∧
      (∀ p q, projectiveIncidenceCoefficient T base radius p (q + 1) =
        projectiveIncidenceCoefficient T base radius (p + 1) q) :=
  polarizedGreenCoefficientEquation_iff_boundary_transport moments _

/-- Once a specified injective realization satisfies the moment equation,
the stage-one native independence supplies both strict parity families. The
remaining moment hypothesis is visible in the statement. -/
theorem realHPCarrierCertificate_of_projectiveMomentEquation
    (T : LinearMap.range nativeIncidenceProjectiveMap →ₗ[ℝ] E)
    (hT : Function.Injective T)
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (hmoment : ProjectiveIncidenceMomentEquation
      canonicalCompletedNativeLogDerivativeMoment T base radius) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    CompletedNativeRealHPCarrierCertificate
      (polarizedCoefficientParityJet (projectiveIncidenceRawJet T base radius)) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hcomplex := complexGreenWronskianMomentKernel_of_vectorCoefficientEquation
    (show HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      (projectiveIncidenceRawJet T base radius) from hmoment)
  let L : (ℕ →₀ ℝ) →ₗ[ℝ] E := T.comp nativeIncidenceProjectiveEquivRange.toLinearMap
  have hL : Function.Injective L := hT.comp nativeIncidenceProjectiveEquivRange.injective
  refine { momentKernel := ?_, evenIndependent := ?_, oddIndependent := ?_ }
  · intro i j
    change greenWronskianMomentKernel canonicalCompletedNativeLogDerivativeMoment i j =
      (inner ℂ (polarizedCoefficientParityJet (projectiveIncidenceRawJet T base radius) i)
        (polarizedCoefficientParityJet (projectiveIncidenceRawJet T base radius) j)).re
    have h := congrArg Complex.re (hcomplex i j)
    simpa using h
  · change LinearIndependent ℝ (fun n : ℕ => L (cameraBracketIncidence base radius (2 * n)))
    exact (evenCameraBracketIncidence_linearIndependent_global hbase hradius).map_injOn L hL.injOn
  · change LinearIndependent ℝ (fun n : ℕ => L (cameraBracketIncidence base radius (2 * n + 1)))
    exact (oddCameraBracketIncidence_linearIndependent_global hbase hradius).map_injOn L hL.injOn

/-- For the stage-one Hilbert realization the entire projective path returns
the original literal vertical bracket, including its original metric. -/
@[simp] theorem projectiveIncidenceRawJet_coreToHilbert (base radius n : ℕ) :
    projectiveIncidenceRawJet nativeProjectiveCoreToHilbert base radius n =
      br2CameraBracketVerticalState base radius n :=
  nativeProjectiveCoreToHilbert_bracket base radius n

/-- First off-diagonal coefficient of total degree two in the C3 realization. -/
theorem c3_rawCoefficient_zero_two :
    projectiveIncidenceCoefficient nativeProjectiveCoreToHilbert 3 1 0 2 = 0 := by
  simp [projectiveIncidenceCoefficient, br2CameraBracketVerticalState,
    inner_add_left, lp.inner_single_left]

/-- The middle coefficient of the same total degree is the bracket norm. -/
theorem c3_rawCoefficient_one_one :
    projectiveIncidenceCoefficient nativeProjectiveCoreToHilbert 3 1 1 1 = 6 := by
  simp only [projectiveIncidenceCoefficient, projectiveIncidenceRawJet_coreToHilbert,
    br2CameraBracketVerticalState, inner_add_left, inner_add_right,
    lp.inner_single_left]
  norm_num

/-- The literal C3 realization fails the polarized shift equation for every
moment sequence, independently of the values of the native moments. -/
theorem not_c3_rawMomentEquation (moments : ℕ → ℝ) :
    ¬ ProjectiveIncidenceMomentEquation moments nativeProjectiveCoreToHilbert 3 1 := by
  intro h
  have hshift := polarizedGreenCoefficient_transport h 0 1
  change projectiveIncidenceCoefficient nativeProjectiveCoreToHilbert 3 1 0 2 =
    projectiveIncidenceCoefficient nativeProjectiveCoreToHilbert 3 1 1 1 at hshift
  rw [c3_rawCoefficient_zero_two, c3_rawCoefficient_one_one] at hshift
  norm_num at hshift

/-- The obstruction already prevents the real moment Gram required by the
HP interface. The even `(0,1)` entry and odd `(0,0)` entry both represent the
same moment, but the raw C3 metric gives respectively zero and six. -/
theorem not_c3_rawGreenMomentKernel (moments : ℕ → ℝ) :
    letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
      InnerProductSpace.rclikeToReal ℂ CanonicalCompletedTfvdGreenHilbertCarrier
    ¬ IsGreenWronskianMomentKernelGramRepresentation moments
      (br2CameraBracketProjectiveHilbertParityJet 3 1) := by
  letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
    InnerProductSpace.rclikeToReal ℂ CanonicalCompletedTfvdGreenHilbertCarrier
  intro hrep
  have heven := hrep (Sum.inl 0) (Sum.inl 1)
  have hodd := hrep (Sum.inr 0) (Sum.inr 0)
  change moments 1 =
    (inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 2)).re at heven
  change moments 1 =
    (inner ℂ (br2CameraBracketVerticalState 3 1 1)
      (br2CameraBracketVerticalState 3 1 1)).re at hodd
  have h02 : inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 2) = 0 := by
    simpa only [projectiveIncidenceCoefficient,
      projectiveIncidenceRawJet_coreToHilbert] using c3_rawCoefficient_zero_two
  have h11 : inner ℂ (br2CameraBracketVerticalState 3 1 1)
      (br2CameraBracketVerticalState 3 1 1) = 6 := by
    simpa only [projectiveIncidenceCoefficient,
      projectiveIncidenceRawJet_coreToHilbert] using c3_rawCoefficient_one_one
  rw [h02] at heven
  rw [h11] at hodd
  norm_num at heven hodd
  linarith

/-- In particular, the current literal C3 jet cannot instantiate the native
HP certificate. Other realizations of the projective span remain a separate
construction problem. -/
theorem not_c3_rawHPCarrierCertificate :
    letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
      InnerProductSpace.rclikeToReal ℂ CanonicalCompletedTfvdGreenHilbertCarrier
    ¬ CompletedNativeRealHPCarrierCertificate
      (br2CameraBracketProjectiveHilbertParityJet 3 1) := by
  letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
    InnerProductSpace.rclikeToReal ℂ CanonicalCompletedTfvdGreenHilbertCarrier
  intro h
  exact not_c3_rawGreenMomentKernel canonicalCompletedNativeLogDerivativeMoment h.momentKernel

end ProjectiveValve

end
end CarrySelfAdjointOperator

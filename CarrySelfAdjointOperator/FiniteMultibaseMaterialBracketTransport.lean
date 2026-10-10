import CarrySelfAdjointOperator.FiniteMultibaseMaterialJetTower

/-! Vector-valued seed/interior bracket synthesis before any readout.
Material position, camera label, derivative order and C2 core/depth remain
distinct. The sample amplitude is an input vector in the existing carrier. -/

noncomputable section
open scoped BigOperators
namespace CarrySelfAdjointOperator.MaterialCameraJets
open CPFormal.Analytic.Cp FiniteClockJets
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Limits

/-- Literal stencil acting diagonally on all material samples, with no scalar sum. -/
def stencilMaterialAction {N : ℕ} (x : FiniteRealSpectralHilbert N) :
    FormalStencil →ₗ[ℤ] FiniteRealSpectralHilbert N where
  toFun f := WithLp.toLp 2 (fun n => (f (n.val + 1) : ℂ) * x n)
  map_add' f g := by ext n; simp [add_mul]
  map_smul' a f := by ext n; simp [mul_assoc]

/-- Camera row mask applied to the supplied full physical vector. -/
def cameraMaterialAction {N : ℕ} (b M : ℕ) (x : FiniteRealSpectralHilbert N) :
    FiniteRealSpectralHilbert N := stencilMaterialAction x (finiteStencil b M)

theorem cameraMaterialAction_apply {N : ℕ} (b M : ℕ)
    (x : FiniteRealSpectralHilbert N) (n : Fin N) :
    cameraMaterialAction b M x n = (finiteCoefficient b M (n.val + 1) : ℂ) * x n := by
  simp [cameraMaterialAction, stencilMaterialAction, finiteStencil_apply]

/-- Literal row vectors are the unit-sample specialization of the geometric mask. -/
theorem literalCameraVector_eq_stencilMaterialAction {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (b : ι) :
    literalCameraVector M camera b =
      cameraMaterialAction (camera b) M (WithLp.toLp 2 (fun _ => (1 : ℂ))) := by
  ext n
  simp [literalCameraVector, cameraMaterialAction_apply, finiteLiteralCameraMatrix,
    finiteCoefficientAt]

/-- The unchanged material log clock commutes with every literal diagonal mask. -/
theorem materialJet_stencilMaterialAction {N : ℕ} (r : ℕ)
    (x : FiniteRealSpectralHilbert N) (f : FormalStencil) :
    materialJet r (stencilMaterialAction x f) =
      stencilMaterialAction (materialJet r x) f := by
  ext n
  simp [materialJet_apply, stencilMaterialAction]
  ring

/-- All cameras: complete vector jets split into their literal seed and all center brackets. -/
theorem cameraMaterialJet_eq_seed_add_centerSum {N : ℕ} (b M r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    materialJet r (cameraMaterialAction b M x) =
      stencilMaterialAction (materialJet r x) (seedStencil b) +
        ∑ j ∈ Finset.range M,
          stencilMaterialAction (materialJet r x) (centerStencil b j) := by
  rw [cameraMaterialAction, materialJet_stencilMaterialAction, finiteStencil,
    map_add, map_sum]

/-- Every natural radius channel, including the antipodal one, survives vector synthesis. -/
theorem cameraMaterialJet_eq_seed_add_radiusSum {N : ℕ} (b M r : ℕ)
    (hb : b ≠ 2) (x : FiniteRealSpectralHilbert N) :
    materialJet r (cameraMaterialAction b M x) =
      stencilMaterialAction (materialJet r x) (seedStencil b) +
        ∑ j ∈ Finset.range M, ∑ radius ∈ FiniteNativeCarryOperator.Camera.radiusSet b,
          stencilMaterialAction (materialJet r x)
            (centeredBracketStencil (FiniteNativeCarryOperator.Camera.alignedCenter b j) radius) := by
  rw [cameraMaterialJet_eq_seed_add_centerSum]
  simp [centerStencil, hb, map_sum]

/-- C2 has its proved geometric core/depth address, rather than a base-general extrapolation. -/
theorem c2MaterialJet_eq_seed_add_fiberVectorSum {N : ℕ} (M r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    materialJet r (cameraMaterialAction 2 M x) =
      stencilMaterialAction (materialJet r x) (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          stencilMaterialAction (materialJet r x)
            (centeredBracketStencil
              (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1) := by
  rw [cameraMaterialJet_eq_seed_add_centerSum]
  simp_rw [c2CenterStencil_eq_fiberBracketStencil]

/-- Independently defined native Dirichlet samples on the finite material prefix. -/
def finiteDirichletSamples (N : ℕ) (s : ℂ) : FiniteRealSpectralHilbert N :=
  WithLp.toLp 2 (fun n => realDirichletPower s ((n.val + 1 : ℕ) : ℝ))

/-- Clock powers agree coordinatewise with the existing all-order logarithmic observable. -/
theorem materialJet_dirichletSamples_apply (N r : ℕ) (s : ℂ) (n : Fin N) :
    materialJet r (finiteDirichletSamples N s) n =
      realLogPowerDirichletPower r s ((n.val + 1 : ℕ) : ℝ) := by
  simp [materialJet_apply, finiteDirichletSamples, finiteRealSpectralFrequency,
    realLogPowerDirichletPower]

/-- Full material vector formula for literal all-order camera samples. -/
theorem cameraMaterialJet_dirichletSamples_apply (N b M r : ℕ) (s : ℂ) (n : Fin N) :
    materialJet r (cameraMaterialAction b M (finiteDirichletSamples N s)) n =
      (finiteCoefficient b M (n.val + 1) : ℂ) *
        realLogPowerDirichletPower r s ((n.val + 1 : ℕ) : ℝ) := by
  rw [cameraMaterialAction, materialJet_stencilMaterialAction]
  simp [stencilMaterialAction, finiteStencil_apply, materialJet_dirichletSamples_apply]

/-- C2 retains the seed and every core/depth bracket at every material jet order. -/
theorem c2MaterialDirichletJet_eq_seed_add_fiberVectors (N M r : ℕ) :
    materialJet r (cameraMaterialAction 2 M (finiteDirichletSamples N (1/2))) =
      stencilMaterialAction (materialJet r (finiteDirichletSamples N (1/2))) (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          stencilMaterialAction (materialJet r (finiteDirichletSamples N (1/2)))
            (centeredBracketStencil
              (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1) :=
  c2MaterialJet_eq_seed_add_fiberVectorSum M r _

end CarrySelfAdjointOperator.MaterialCameraJets

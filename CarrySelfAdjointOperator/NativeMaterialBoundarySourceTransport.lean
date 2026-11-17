import CarrySelfAdjointOperator.NativeMaterialCameraBoundary
import CarrySelfAdjointOperator.NativePhysicalCameraCrossings

/-! The integer border identity in the original material and completed
carriers. All material samples and both completed source legs are synthesized
before pairing. Source positivity is neither assumed nor concluded. -/
namespace CarrySelfAdjointOperator.MaterialBoundarySewing
open CPFormal.Analytic.Cp MaterialCameraJets PhysicalSewing NativeCauchyPorts NativeLaguerre
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Limits
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

def coreMaterialJet {N : ℕ} (b M r : ℕ) (x : FiniteRealSpectralHilbert N) :=
  stencilMaterialAction (materialJet r x) (cameraCoreStencil b M)

def borderMaterialJet {N : ℕ} (b M r : ℕ) (x : FiniteRealSpectralHilbert N) :=
  stencilMaterialAction (materialJet r x) (cameraBorderStencil b M)

/-- The original material clock and arbitrary complex samples, before
discarding either real quadrature. Position and temporal order are separate. -/
theorem materialCameraJet_core_border {N : ℕ} (b M r : ℕ) (hb : 2 ≤ b)
    (x : FiniteRealSpectralHilbert N) :
    materialJet r (cameraMaterialAction b M x) =
      coreMaterialJet b M r x + borderMaterialJet b M r x := by
  rw [cameraMaterialAction,materialJet_stencilMaterialAction,
    finiteStencil_eq_core_add_border b M hb,map_add]
  rfl

/-- Actual temporal derivatives keep their forced complex phase. -/
theorem materialCameraTemporalJet_core_border {N : ℕ} (b M r : ℕ) (hb : 2 ≤ b)
    (x : FiniteRealSpectralHilbert N) :
    iteratedDeriv r (fun t : ℝ => FiniteClockJets.finiteMaterialOrbit N t
      (cameraMaterialAction b M x)) 0 =
      (-Complex.I)^r • (coreMaterialJet b M r x+borderMaterialJet b M r x) := by
  rw [materialOrbit_derivative_eq_phasedJet,materialCameraJet_core_border b M r hb]

def cameraMaterialFamily {ι : Type*} [Fintype ι] {N : ℕ}
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) (a : ι → ℂ) (x : FiniteRealSpectralHilbert N) :=
  ∑ b, a b • materialJet r (cameraMaterialAction (camera b) M x)

def coreMaterialFamily {ι : Type*} [Fintype ι] {N : ℕ}
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) (a : ι → ℂ) (x : FiniteRealSpectralHilbert N) :=
  ∑ b, a b • coreMaterialJet (camera b) M r x

def borderMaterialFamily {ι : Type*} [Fintype ι] {N : ℕ}
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) (a : ι → ℂ) (x : FiniteRealSpectralHilbert N) :=
  ∑ b, a b • borderMaterialJet (camera b) M r x

theorem cameraMaterialFamily_core_border {ι : Type*} [Fintype ι] {N : ℕ}
    (M : ℕ) (camera : ι → ℕ) (hc : ∀ b, 2 ≤ camera b)
    (r : ℕ) (a : ι → ℂ) (x : FiniteRealSpectralHilbert N) :
    cameraMaterialFamily M camera r a x =
      coreMaterialFamily M camera r a x + borderMaterialFamily M camera r a x := by
  simp only [cameraMaterialFamily,coreMaterialFamily,borderMaterialFamily,
    materialCameraJet_core_border _ _ _ (hc _),smul_add,Finset.sum_add_distrib]

/-- Actual source transport, using the existing completed columns, with no
moment data in its coefficients and no new Hilbert metric. -/
def completedMaterialTransport (N k : ℕ) :
    FiniteRealSpectralHilbert N →ₗ[ℂ] CanonicalCompletedNativeProjectiveChiralCarrier where
  toFun x := finiteProjectiveSource N k (fun j => x j)
  map_add' x y := by
    simp [finiteProjectiveSource,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by
    simp [finiteProjectiveSource,Finset.smul_sum,mul_smul]

/-- The endpoint derivative chart has its own order index. It produces
exactly the pre-existing source input; material addresses are not silently
declared to be radial derivative orders. -/
theorem completedMaterialTransport_source_chart (n k : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    completedMaterialTransport (2*n) k x =
      nativeSourceProjectiveBoundaryJetSynthesis n k
        (physicalEndpointJetInput (2*n) k (fun j => x j)) :=
  (physicalEndpointJetInput_wholeSource n k (fun j => x j)).symm

theorem completedMaterialTransport_camera_family {ι : Type*} [Fintype ι] (N k M : ℕ)
    (camera : ι → ℕ) (hc : ∀ b, 2 ≤ camera b) (r : ℕ) (a : ι → ℂ)
    (x : FiniteRealSpectralHilbert N) :
    completedMaterialTransport N k (cameraMaterialFamily M camera r a x) =
      completedMaterialTransport N k (coreMaterialFamily M camera r a x) +
        completedMaterialTransport N k (borderMaterialFamily M camera r a x) := by
  rw [cameraMaterialFamily_core_border M camera hc,map_add]

/-- Full polarization for two independent labels, coefficient families,
clock orders and material inputs. All four core/border sectors survive. -/
theorem completed_camera_two_inputs {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N k M L : ℕ) (b : ι → ℕ) (c : κ → ℕ)
    (hb : ∀ i, 2 ≤ b i) (hc : ∀ j, 2 ≤ c j)
    (r s : ℕ) (a : ι → ℂ) (z : κ → ℂ) (x y : FiniteRealSpectralHilbert N) :
    canonicalCompletedNativeProjectiveChiralForm
      (completedMaterialTransport N k (cameraMaterialFamily M b r a x))
      (completedMaterialTransport N k (cameraMaterialFamily L c s z y)) =
      ∑ i, ∑ j, conj (a i)*z j *
        (canonicalCompletedNativeProjectiveChiralForm
            (completedMaterialTransport N k (coreMaterialJet (b i) M r x))
            (completedMaterialTransport N k (coreMaterialJet (c j) L s y)) +
          canonicalCompletedNativeProjectiveChiralForm
            (completedMaterialTransport N k (coreMaterialJet (b i) M r x))
            (completedMaterialTransport N k (borderMaterialJet (c j) L s y)) +
          canonicalCompletedNativeProjectiveChiralForm
            (completedMaterialTransport N k (borderMaterialJet (b i) M r x))
            (completedMaterialTransport N k (coreMaterialJet (c j) L s y)) +
          canonicalCompletedNativeProjectiveChiralForm
            (completedMaterialTransport N k (borderMaterialJet (b i) M r x))
            (completedMaterialTransport N k (borderMaterialJet (c j) L s y))) := by
  rw [cameraMaterialFamily_core_border M b hb,cameraMaterialFamily_core_border L c hc]
  simp only [map_add,coreMaterialFamily,borderMaterialFamily,map_sum,map_smul,
    ← Finset.sum_add_distrib]
  rw [physicalPair_camera_fourSectors]
  simp only [projectiveChiralForm_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Literal stencil producer in the OLD two-leg carrier, with its source
amplitude, analytic response and return. -/
theorem originalMaterialSource_core_border (k b M : ℕ) (hb : 2 ≤ b) :
    originalMaterialCompletedSource k (finiteStencil b M) =
      originalMaterialCompletedSource k (cameraCoreStencil b M) +
        originalMaterialCompletedSource k (cameraBorderStencil b M) := by
  rw [finiteStencil_eq_core_add_border b M hb,map_add]

/-- Lossless window chosen from the actual material polynomial. This
connects the literal stencil to the original jet INPUT, not only its output. -/
theorem originalCamera_source_input_core_border (k b M : ℕ) (hb : 2 ≤ b) :
    let stencil := finiteStencil b M
    nativeSourceProjectiveBoundaryJetSynthesis (materialStencilHalfWindow stencil) k
      (physicalEndpointJetInput (2*materialStencilHalfWindow stencil) k
        (materialStencilCoefficients stencil)) =
      originalMaterialCompletedSource k (cameraCoreStencil b M) +
        originalMaterialCompletedSource k (cameraBorderStencil b M) := by
  dsimp only
  rw [physicalEndpointJetInput_wholeSource]
  have he : originalMaterialCompletedSource k (finiteStencil b M) =
      finiteProjectiveSource (2*materialStencilHalfWindow (finiteStencil b M)) k
        (materialStencilCoefficients (finiteStencil b M)) := by
    rw [originalMaterialCompletedSource_eq_physical,materialStencilRadialCoefficients_eq_fin,
      physicalCompletedFiniteSource_fin]
  rw [← he]
  exact originalMaterialSource_core_border k b M hb

/-- The border is a concrete sum of original completed source columns. -/
theorem originalMaterialSource_border_columns (k b M : ℕ) :
    originalMaterialCompletedSource k (cameraBorderStencil b M) =
      ∑ r ∈ Finset.range (cameraBoundaryWidth b),
        canonicalCompletedNativeRadialProjectiveChiralState k (cameraSlope b*M+r) := by
  simp [cameraBorderStencil,unitBorderStencil,originalMaterialCompletedSource_atom]

def cameraPieceStencil (b M : ℕ) : Fin 2 → FormalStencil :=
  ![cameraCoreStencil b M,cameraBorderStencil b M]

/-- Green and the analytic residual are independently defined ORIGINAL
operators. The residual is retained in each material piece. -/
def physicalGreenPiece (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ)
    (stencil : FormalStencil) : Fin 2 → CanonicalCompletedNativeProjectiveChiralCarrier :=
  ![(q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
      (physicalGreenBulkBoundary q k (materialStencilRadialCoefficients stencil)),
    (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
      (physicalGreenResidualNumerator q k (materialStencilRadialCoefficients stencil))]

theorem physicalGreenPiece_synthesis (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (k : ℕ) (stencil : FormalStencil) :
    (∑ t : Fin 2, physicalGreenPiece q hq0 hq1 k stencil t) =
      originalMaterialCompletedSource k stencil := by
  rw [Fin.sum_univ_two]
  simp only [physicalGreenPiece,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [← smul_add,← map_add]
  exact ((originalMaterial_wholeSource_capstone k stencil q hq0 hq1).2).symm

/-- Four physical channels: core/border times Green/analytic residual.
They reconstruct the whole original pair before any form is evaluated. -/
theorem originalCamera_four_vector_channels (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (k b M : ℕ) (hb : 2 ≤ b) :
    originalMaterialCompletedSource k (finiteStencil b M) =
      ∑ piece : Fin 2, ∑ t : Fin 2,
        physicalGreenPiece q hq0 hq1 k (cameraPieceStencil b M piece) t := by
  simp_rw [physicalGreenPiece_synthesis]
  simp only [Fin.sum_univ_two,cameraPieceStencil,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact originalMaterialSource_core_border k b M hb

def completedStencilFamily {ι : Type*} [Fintype ι] (k M : ℕ)
    (camera : ι → ℕ) (a : ι → ℂ) : CanonicalCompletedNativeProjectiveChiralCarrier :=
  ∑ b, a b • originalMaterialCompletedSource k (finiteStencil (camera b) M)

def cameraFourChannels {ι : Type*} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (k M : ℕ) (camera : ι → ℕ) (a : ι → ℂ)
    (p : ι × (Fin 2 × Fin 2)) : CanonicalCompletedNativeProjectiveChiralCarrier :=
  a p.1 • physicalGreenPiece q hq0 hq1 k (cameraPieceStencil (camera p.1) M p.2.1) p.2.2

theorem cameraFourChannels_synthesis {ι : Type*} [Fintype ι]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (k M : ℕ)
    (camera : ι → ℕ) (hc : ∀ b, 2 ≤ camera b) (a : ι → ℂ) :
    completedStencilFamily k M camera a =
      ∑ p : ι × (Fin 2 × Fin 2), cameraFourChannels q hq0 hq1 k M camera a p := by
  rw [Fintype.sum_prod_type]
  unfold completedStencilFamily
  apply Finset.sum_congr rfl
  intro b _
  rw [originalCamera_four_vector_channels q hq0 hq1 k (camera b) M (hc b)]
  simp only [cameraFourChannels,Fintype.sum_prod_type,Finset.smul_sum]

/-- Every ordered camera cross and every GG/GR/RG/RR term for each
core/border pair. In particular no analytic residual is set to zero. -/
theorem completedStencilFamily_signed_sixteen_sectors
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (k M L : ℕ)
    (b : ι → ℕ) (c : κ → ℕ) (hb : ∀ i, 2 ≤ b i) (hc : ∀ j, 2 ≤ c j)
    (a : ι → ℂ) (z : κ → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (completedStencilFamily k M b a) (completedStencilFamily k L c z) =
      ∑ i : ι × (Fin 2 × Fin 2), ∑ j : κ × (Fin 2 × Fin 2),
        canonicalCompletedNativeProjectiveChiralForm
          (cameraFourChannels q hq0 hq1 k M b a i)
          (cameraFourChannels q hq0 hq1 k L c z j) := by
  rw [cameraFourChannels_synthesis q hq0 hq1 k M b hb a,
    cameraFourChannels_synthesis q hq0 hq1 k L c hc z,
    physicalPair_signed_camera_crosses]

end
end CarrySelfAdjointOperator.MaterialBoundarySewing

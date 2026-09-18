import CarrySelfAdjointOperator.CompletedNativeGeometryHeightProvenance
import CarrySelfAdjointOperator.CompletedNativeHPGateAudit
import CarrySelfAdjointOperator.BR2ProjectiveHilbertIncidenceTransport
import CarrySelfAdjointOperator.BR2GreenFrameDslopeLimitBridge
import Mathlib.Tactic

/-!
# Isometric native Green--incidence bridge

The completed Green forward-difference limit already carries the exact
Green--Wronskian Gram.  The projective BR2 carrier already carries the
injective incidence transport.  This file records the precise fact that an
isometric identification of the two jets is enough: it preserves every Gram
entry and transports the incidence map without introducing a new kernel,
Hankel matrix, Jacobi matrix, or radial Taylor carrier.

The remaining concrete gate is therefore isolated as one vector-valued
isometry/jet identification.  Once supplied, the existing finite height
constructor and its symmetry theorem apply unchanged.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera

noncomputable section

/-! ## Isometric transport of the already formalized incidence certificate -/

/-- Compose an existing native incidence transport with a real linear
isometry.  The target family is the image family, and injectivity is retained
without changing any incidence vector or adding a positivity assumption. -/
def BR2BracketIncidenceJetTransport.map_isometry
    {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    {base radius : ℕ} {jet : (ℕ ⊕ ℕ) → E}
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (U : E →ₗᵢ[ℝ] E') :
    BR2BracketIncidenceJetTransport base radius (fun i => U (jet i)) where
  toLinearMap := U.toLinearMap.comp transport.toLinearMap
  injective := U.injective.comp transport.injective
  even_eq n := by
    change U (jet (Sum.inl n)) =
      U (transport.toLinearMap
        (cameraBracketIncidence base radius (2 * n)))
    rw [transport.even_eq]
  odd_eq n := by
    change U (jet (Sum.inr n)) =
      U (transport.toLinearMap
        (cameraBracketIncidence base radius (2 * n + 1)))
    rw [transport.odd_eq]

@[simp] theorem BR2BracketIncidenceJetTransport.map_isometry_toLinearMap_apply
    {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    {base radius : ℕ} {jet : (ℕ ⊕ ℕ) → E}
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (U : E →ₗᵢ[ℝ] E') (v : ℕ →₀ ℝ) :
    (transport.map_isometry U).toLinearMap v =
      U (transport.toLinearMap v) :=
  rfl

/-- A real linear isometry preserves the inner-product Gram entry-by-entry.
This is the exact pre-Hankel statement used by the native crosswalk. -/
theorem linearIsometry_gram_entry
    {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    {ι : Type*} (jet : ι → E) (U : E →ₗᵢ[ℝ] E') (i j : ι) :
    inner ℝ (U (jet i)) (U (jet j)) = inner ℝ (jet i) (jet j) :=
  U.inner_map_map (jet i) (jet j)

theorem linearIsometry_gram
    {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    {ι : Type*} (jet : ι → E) (U : E →ₗᵢ[ℝ] E') :
    Matrix.gram ℝ (fun i => U (jet i)) = Matrix.gram ℝ jet := by
  ext i j
  exact linearIsometry_gram_entry jet U i j

/-- Pull a Green--Wronskian Gram representation back through a real linear
isometry.  This is the abstract form of the pre-Hankel identification: the
kernel is already realized by the image jet, and the isometry transfers that
same kernel to the native source jet. -/
theorem isGreenWronskianMomentKernelGramRepresentation_of_isometricImage
    {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    {moments : ℕ → ℝ}
    {jet : (ℕ ⊕ ℕ) → E} {image : (ℕ ⊕ ℕ) → E'}
    (U : E →ₗᵢ[ℝ] E')
    (himage : ∀ i, U (jet i) = image i)
    (hgreen : IsGreenWronskianMomentKernelGramRepresentation moments image) :
    IsGreenWronskianMomentKernelGramRepresentation moments jet := by
  intro i j
  change greenWronskianMomentKernel moments i j =
    inner ℝ (jet i) (jet j)
  have hgreen' := hgreen i j
  change greenWronskianMomentKernel moments i j =
    inner ℝ (image i) (image j) at hgreen'
  calc
    greenWronskianMomentKernel moments i j =
        inner ℝ (image i) (image j) := hgreen'
    _ = inner ℝ (U (jet i)) (U (jet j)) := by
      rw [himage i, himage j]
    _ = inner ℝ (jet i) (jet j) := U.inner_map_map (jet i) (jet j)

/-! ## Concrete completed-native specialization -/

/-! ## Wronskian-first native handoff -/

/- The existing Green-frame bridge already expresses the native comparison at
the correct level: a vector defect in the common analyzed carrier.  Once this
defect vanishes, the exact Green-limit jet is the incidence jet, before any
Hankel or Jacobi object is formed. -/

theorem canonicalCompletedNativeGreenLimitJet_eq_projective_of_greenFrameDefect
    {base radius : ℕ}
    (state : ℂ → CanonicalCompletedTfvdGreenHilbertCarrier)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (hdefect : HasCanonicalCompletedNativeGreenFrameDslopeBR2DefectLimit
      state base radius) :
    canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state hkernel =
      br2CameraBracketProjectiveHilbertParityJet base radius := by
  have hanal :
      canonicalCompletedNativeGreenFrameDslopeJet state hkernel =
        br2CameraBracketGreenFrameParityJet base radius :=
    (canonicalCompletedNativeGreenFrameDslopeJet_eq_br2_iff_defect_tendsto_zero
      state hkernel base radius).mpr hdefect
  exact
    (canonicalCompletedNativeGreenFrameDslopeJet_eq_br2_iff
      state hkernel base radius).mp hanal

/- The preceding vector identity is exactly the input required by the
already-built native transport constructor.  The result is the same
Green--Wronskian moment kernel and the same incidence certificate, with no
new positive proxy. -/

theorem nativeGeometry_to_finiteHeight_chain_of_greenFrameDefect
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (state : ℂ → CanonicalCompletedTfvdGreenHilbertCarrier)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (hdefect : HasCanonicalCompletedNativeGreenFrameDslopeBR2DefectLimit
      state base radius)
    (cutoff N : ℕ) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      normalizedCompletedNativeCameraCharacteristic 3 cutoff =
          (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
        completedNativeCameraLogDerivativeMoment 3 cutoff =
          canonicalCompletedNativeLogDerivativeMoment ∧
        (∃ hgram :
            (hankelGram
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N).PosDef,
          canonicalFiniteJacobiSection
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N hgram =
            canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
        (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
    InnerProductSpace.rclikeToReal ℂ _
  let transport :=
    CarrySelfAdjointOperator.canonicalCompletedNativeRealTfvdGreenMomentTransport_of_greenFrameDefect
      state hkernel hdefect
  exact nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport
    hbase hradius transport.momentKernel transport.incidenceTransport
    cutoff N

/-- The concrete projective-to-Green isometry gate.  Its conclusion is the
same typed transport object consumed by the existing HP gate: the jet is the
canonical completed Green limit, its Gram is the proved native moment kernel,
and its incidence independence is inherited through the isometry. -/
def canonicalCompletedNativeRealTfvdGreenMomentTransport_of_isometricProjectiveJet
    {base radius : ℕ}
    (state : ℂ → CanonicalCompletedTfvdGreenHilbertCarrier)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (U : CanonicalCompletedTfvdGreenHilbertCarrier →ₗᵢ[ℝ]
      CanonicalCompletedTfvdGreenHilbertCarrier)
    (hjet : ∀ i : ℕ ⊕ ℕ,
      U (br2CameraBracketProjectiveHilbertParityJet base radius i) =
        canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          state hkernel i) :
    CanonicalCompletedNativeRealTfvdGreenMomentTransport base radius := by
  let projectiveTransport :=
    br2CameraBracketProjectiveHilbertIncidenceJetTransport base radius
  let imageTransport := projectiveTransport.map_isometry U
  have hfamily :
      (fun i : ℕ ⊕ ℕ => U
        (br2CameraBracketProjectiveHilbertParityJet base radius i)) =
        canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          state hkernel := by
    funext i
    exact hjet i
  refine
    { jet := canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state hkernel
      incidenceTransport := ?_
      momentKernel := ?_ }
  · rw [← hfamily]
    exact imageTransport
  · exact canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
      state hkernel

/-- The same isometric gate can be read in the native projective carrier
before passing to the height constructor: the projective incidence jet itself
then realizes the exact Green--Wronskian moment kernel. -/
theorem canonicalCompletedNativeProjectiveJet_isGreenMomentKernel_of_isometry
    {base radius : ℕ}
    (state : ℂ → CanonicalCompletedTfvdGreenHilbertCarrier)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (U : CanonicalCompletedTfvdGreenHilbertCarrier →ₗᵢ[ℝ]
      CanonicalCompletedTfvdGreenHilbertCarrier)
    (hjet : ∀ i : ℕ ⊕ ℕ,
      U (br2CameraBracketProjectiveHilbertParityJet base radius i) =
        canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          state hkernel i) :
    letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
      InnerProductSpace.rclikeToReal ℂ _
    IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment
      (br2CameraBracketProjectiveHilbertParityJet base radius) := by
  letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
    InnerProductSpace.rclikeToReal ℂ _
  apply isGreenWronskianMomentKernelGramRepresentation_of_isometricImage
    (jet := br2CameraBracketProjectiveHilbertParityJet base radius)
    (image := canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
      state hkernel)
    U hjet
  exact canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
    state hkernel

/-- The raw projective incidence jet cannot be related to the normalized
Green-limit jet by a real linear isometry: the native center pivot already
forces a strictly larger `(0,0)` Gram entry.  Thus the isometric bridge above
is a valid transport lemma, but not a candidate for the unnormalised raw
projective carrier. -/
theorem not_exists_isometricProjectiveJet_identification
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (state : ℂ → CanonicalCompletedTfvdGreenHilbertCarrier)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    ¬ ∃ U : CanonicalCompletedTfvdGreenHilbertCarrier →ₗᵢ[ℝ]
        CanonicalCompletedTfvdGreenHilbertCarrier,
      ∀ i : ℕ ⊕ ℕ,
        U (br2CameraBracketProjectiveHilbertParityJet base radius i) =
          canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
            state hkernel i := by
  letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
    InnerProductSpace.rclikeToReal ℂ _
  rintro ⟨U, hjet⟩
  have hlimit :=
    canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
      state hkernel (Sum.inl 0) (Sum.inl 0)
  change canonicalCompletedNativeLogDerivativeMoment 0 =
    inner ℝ
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state hkernel (Sum.inl 0))
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state hkernel (Sum.inl 0)) at hlimit
  have hprojective :
      canonicalCompletedNativeLogDerivativeMoment 0 <
        inner ℝ
          (br2CameraBracketProjectiveHilbertParityJet base radius
            (Sum.inl 0))
          (br2CameraBracketProjectiveHilbertParityJet base radius
            (Sum.inl 0)) := by
    change canonicalCompletedNativeLogDerivativeMoment 0 <
      inner ℝ
        (br2CameraBracketVerticalState base radius 0)
        (br2CameraBracketVerticalState base radius 0)
    simp only [real_inner_self_eq_norm_sq]
    have hcoord := lp.norm_apply_le_norm
      (by norm_num : (2 : ENNReal) ≠ 0)
      (br2CameraBracketVerticalState base radius 0)
      (alignedCenter base 0)
    rw [br2CameraBracketVerticalState_apply_alignedCenter
      hbase hradius 0 0] at hcoord
    norm_num at hcoord ⊢
    have hmoment := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
    nlinarith [sq_nonneg
      (‖br2CameraBracketVerticalState base radius 0‖ - 2)]
  have htransport :
      inner ℝ
          (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
            state hkernel (Sum.inl 0))
          (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
            state hkernel (Sum.inl 0)) =
        inner ℝ
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0))
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0)) := by
    calc
      inner ℝ
          (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
            state hkernel (Sum.inl 0))
          (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
            state hkernel (Sum.inl 0)) =
          inner ℝ
            (U (br2CameraBracketProjectiveHilbertParityJet base radius
              (Sum.inl 0)))
            (U (br2CameraBracketProjectiveHilbertParityJet base radius
              (Sum.inl 0))) := by
        rw [hjet (Sum.inl 0)]
      _ = inner ℝ
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0))
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0)) :=
        U.inner_map_map _ _
  linarith

/-- End-to-end version using the projective carrier itself.  The isometry is
used only to pull the already-proved Green-limit Gram back to the native
incidence jet; the original incidence transport is then passed unchanged to
the height theorem. -/
theorem nativeGeometry_to_finiteHeight_chain_of_isometricProjectiveJet_on_projectiveCarrier
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (state : ℂ → CanonicalCompletedTfvdGreenHilbertCarrier)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (U : CanonicalCompletedTfvdGreenHilbertCarrier →ₗᵢ[ℝ]
      CanonicalCompletedTfvdGreenHilbertCarrier)
    (hjet : ∀ i : ℕ ⊕ ℕ,
      U (br2CameraBracketProjectiveHilbertParityJet base radius i) =
        canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          state hkernel i)
    (cutoff N : ℕ) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      normalizedCompletedNativeCameraCharacteristic 3 cutoff =
          (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
        completedNativeCameraLogDerivativeMoment 3 cutoff =
          canonicalCompletedNativeLogDerivativeMoment ∧
        (∃ hgram :
            (hankelGram
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N).PosDef,
          canonicalFiniteJacobiSection
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N hgram =
            canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
        (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
    InnerProductSpace.rclikeToReal ℂ _
  have hgreen := canonicalCompletedNativeProjectiveJet_isGreenMomentKernel_of_isometry
    state hkernel U hjet
  exact nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport
    hbase hradius hgreen
    (br2CameraBracketProjectiveHilbertIncidenceJetTransport base radius)
    cutoff N

/-- The isometric projective-to-Green identification gives equality of the
native projective and Green-limit Gram matrices before any Hankel/Jacobi
construction. -/
theorem canonicalCompletedNativeGreenLimitGram_eq_projectiveGram_of_isometry
    {base radius : ℕ}
    (state : ℂ → CanonicalCompletedTfvdGreenHilbertCarrier)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (U : CanonicalCompletedTfvdGreenHilbertCarrier →ₗᵢ[ℝ]
      CanonicalCompletedTfvdGreenHilbertCarrier)
    (hjet : ∀ i : ℕ ⊕ ℕ,
      U (br2CameraBracketProjectiveHilbertParityJet base radius i) =
        canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          state hkernel i) :
    Matrix.gram ℝ
        (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          state hkernel) =
      Matrix.gram ℝ (br2CameraBracketProjectiveHilbertParityJet base radius) := by
  have himage :
      (fun i : ℕ ⊕ ℕ => U
        (br2CameraBracketProjectiveHilbertParityJet base radius i)) =
        canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          state hkernel := by
    funext i
    exact hjet i
  rw [← himage]
  exact linearIsometry_gram
    (br2CameraBracketProjectiveHilbertParityJet base radius) U

/-- End-to-end finite consequence of the isometric jet gate: the existing
native camera characteristic/moment crosswalk supplies the common moments,
the Green limit supplies their Gram, incidence supplies strict positivity,
and the resulting finite height operator is symmetric. -/
theorem nativeGeometry_to_finiteHeight_chain_of_isometricProjectiveJet
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (state : ℂ → CanonicalCompletedTfvdGreenHilbertCarrier)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (U : CanonicalCompletedTfvdGreenHilbertCarrier →ₗᵢ[ℝ]
      CanonicalCompletedTfvdGreenHilbertCarrier)
    (hjet : ∀ i : ℕ ⊕ ℕ,
      U (br2CameraBracketProjectiveHilbertParityJet base radius i) =
        canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          state hkernel i)
    (cutoff N : ℕ) :
    ∃ hpos : CanonicalCompletedNativeStieltjesPositivity,
      normalizedCompletedNativeCameraCharacteristic 3 cutoff =
          (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
        completedNativeCameraLogDerivativeMoment 3 cutoff =
          canonicalCompletedNativeLogDerivativeMoment ∧
        (∃ hgram :
            (hankelGram
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N).PosDef,
          canonicalFiniteJacobiSection
              (completedNativeCameraLogDerivativeMoment 3 cutoff) N hgram =
            canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
        (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
    InnerProductSpace.rclikeToReal ℂ _
  let certificate :=
    canonicalCompletedNativeRealTfvdGreenMomentTransport_of_isometricProjectiveJet
      state hkernel U hjet
  exact nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport
    hbase hradius certificate.momentKernel certificate.incidenceTransport
    cutoff N

end

end CarrySelfAdjointOperator

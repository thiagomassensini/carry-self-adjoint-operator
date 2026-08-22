import CarrySelfAdjointOperator.BracketLegLatticeSeparation
import CarrySelfAdjointOperator.CompletedGreenMomentJets
import Mathlib.Tactic

/-!
# BR2 bipartite center--leg moment kernel

The coefficient matrix is indexed by two geometric roles: one aligned center
and one bracket leg.  Equality of formal matrix indices therefore does not
mean equality of the sampled coordinates.

`BracketLegLatticeSeparation` proves the stronger all-base statement needed
here.  Every emitted leg lies outside the aligned-center lattice of its
camera, so every center--leg sample is geometrically off-diagonal, including
samples carrying the same formal index.

This file inserts that fact immediately before the existing
Green--Wronskian/Hankel bridge.  A scalar Green identity stated only for
unequal geometric coordinates can therefore supply every entry of the moment
Gram kernel.  No analytic collision value and no primality assumption are
introduced.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- Which leg of a centered bracket is used by the bipartite readout. -/
inductive BR2CameraLegSide where
  | left
  | right
  deriving DecidableEq

/-- Coordinate of the selected bracket leg. -/
def br2CameraLegCoordinate
    (side : BR2CameraLegSide) (camera index radius : ℕ) : ℕ :=
  match side with
  | .left => alignedCenter camera index - radius
  | .right => alignedCenter camera index + radius

/-- Arithmetic incidence assigning one aligned center and one emitted leg to
every parity-jet index.  The two index maps may be different; lattice
separation does not require them to agree. -/
structure BR2CameraIncidence where
  camera : ℕ
  radius : ℕ
  hcamera : 2 ≤ camera
  hradius : radius ∈ radiusSet camera
  side : BR2CameraLegSide
  centerIndex : (ℕ ⊕ ℕ) → ℕ
  legIndex : (ℕ ⊕ ℕ) → ℕ

namespace BR2CameraIncidence

/-- Center coordinate assigned to a parity-jet index. -/
def centerCoordinate
    (incidence : BR2CameraIncidence) (i : ℕ ⊕ ℕ) : ℕ :=
  alignedCenter incidence.camera (incidence.centerIndex i)

/-- Leg coordinate assigned to a parity-jet index. -/
def legCoordinate
    (incidence : BR2CameraIncidence) (j : ℕ ⊕ ℕ) : ℕ :=
  br2CameraLegCoordinate incidence.side incidence.camera
    (incidence.legIndex j) incidence.radius

/-- Every selected center--leg pair lies off the geometric diagonal.  This
includes equal formal indices. -/
theorem centerCoordinate_ne_legCoordinate
    (incidence : BR2CameraIncidence) (i j : ℕ ⊕ ℕ) :
    incidence.centerCoordinate i ≠ incidence.legCoordinate j := by
  rcases incidence with
    ⟨camera, radius, hcamera, hradius, side, centerIndex, legIndex⟩
  cases side with
  | left =>
      exact
        ((bracketLegs_ne_any_alignedCenter
          (camera := camera) (index := legIndex j)
          (radius := radius) (otherIndex := centerIndex i)
          hcamera hradius).1).symm
  | right =>
      exact
        ((bracketLegs_ne_any_alignedCenter
          (camera := camera) (index := legIndex j)
          (radius := radius) (otherIndex := centerIndex i)
          hcamera hradius).2).symm

/-- Same-index entries remain geometrically off-diagonal. -/
theorem sameIndex_offDiagonal
    (incidence : BR2CameraIncidence) (i : ℕ ⊕ ℕ) :
    incidence.centerCoordinate i ≠ incidence.legCoordinate i :=
  incidence.centerCoordinate_ne_legCoordinate i i

end BR2CameraIncidence

/-- Natural-number label carried by one parity jet. -/
def br2ParityJetNumber : (ℕ ⊕ ℕ) → ℕ
  | Sum.inl n => 2 * n
  | Sum.inr n => 2 * n + 1

/-- Canonical incidence using the parity-jet number on both roles.  Equal
formal indices still select unequal coordinates because the roles are center
and leg. -/
def canonicalParityCenterLegIncidence
    (camera radius : ℕ)
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (side : BR2CameraLegSide) : BR2CameraIncidence where
  camera := camera
  radius := radius
  hcamera := hcamera
  hradius := hradius
  side := side
  centerIndex := br2ParityJetNumber
  legIndex := br2ParityJetNumber

/-- Explicit same-index obstruction for the canonical parity incidence. -/
theorem canonicalParityCenterLeg_sameIndex_offDiagonal
    (camera radius : ℕ)
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (side : BR2CameraLegSide) (i : ℕ ⊕ ℕ) :
    (canonicalParityCenterLegIncidence
        camera radius hcamera hradius side).centerCoordinate i ≠
      (canonicalParityCenterLegIncidence
        camera radius hcamera hradius side).legCoordinate i :=
  (canonicalParityCenterLegIncidence
    camera radius hcamera hradius side).sameIndex_offDiagonal i

/-- A bipartite scalar Green kernel realizing the parity-split moment matrix.

`momentReadout` identifies its coefficients with the Hankel moment kernel.
`greenOffDiagonalReadout` identifies the same scalar values with Hilbert inner
products whenever the two geometric coordinates differ.  The camera
incidence proves that this side condition holds for every matrix entry. -/
structure BR2CenterLegGreenMomentCertificate
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (incidence : BR2CameraIncidence)
    (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → E) where
  scalarKernel : ℕ → ℕ → ℂ
  momentReadout : ∀ i j : ℕ ⊕ ℕ,
    (greenWronskianMomentKernel moments i j : ℂ) =
      scalarKernel
        (incidence.centerCoordinate i)
        (incidence.legCoordinate j)
  greenOffDiagonalReadout : ∀ i j : ℕ ⊕ ℕ,
    incidence.centerCoordinate i ≠ incidence.legCoordinate j →
      scalarKernel
          (incidence.centerCoordinate i)
          (incidence.legCoordinate j) =
        inner ℂ (jet i) (jet j)

namespace BR2CenterLegGreenMomentCertificate

/-- Lattice separation converts the off-diagonal Green identity into the
complete complex moment-kernel Gram representation.  There is no missing
matrix diagonal. -/
theorem toComplexMomentKernel
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {incidence : BR2CameraIncidence}
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (certificate :
      BR2CenterLegGreenMomentCertificate incidence moments jet) :
    IsComplexGreenWronskianMomentKernelGramRepresentation moments jet := by
  intro i j
  calc
    (greenWronskianMomentKernel moments i j : ℂ) =
        certificate.scalarKernel
          (incidence.centerCoordinate i)
          (incidence.legCoordinate j) :=
      certificate.momentReadout i j
    _ = inner ℂ (jet i) (jet j) :=
      certificate.greenOffDiagonalReadout i j
        (incidence.centerCoordinate_ne_legCoordinate i j)

/-- Consequently both finite Hankel sections are positive semidefinite at
every order. -/
theorem hankelPair_posSemidef
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {incidence : BR2CameraIncidence}
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (certificate :
      BR2CenterLegGreenMomentCertificate incidence moments jet)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef :=
  hankelPair_posSemidef_of_complexGreenWronskianMomentKernel
    certificate.toComplexMomentKernel N

end BR2CenterLegGreenMomentCertificate

/-- Concrete certificate type for the actual normalized completed native/C3
product-ledger jets. -/
abbrev CanonicalCompletedNativeBR2CenterLegCertificate
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (camera radius : ℕ)
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (side : BR2CameraLegSide)
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ) :=
  BR2CenterLegGreenMomentCertificate
    (canonicalParityCenterLegIncidence
      camera radius hcamera hradius side)
    moments
    (completedGreenParityJet
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        (completedNativeC3ProductLedgerState xiState)))

/-- End-to-end finite positivity after the two factor Green representations
and the concrete center--leg coefficient certificate are supplied.  The
former analytic diagonal premise has disappeared: every sampled pair is
off-diagonal by camera geometry. -/
theorem hankelPair_posSemidef_of_canonicalCompletedNativeCenterLeg
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (camera radius : ℕ)
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (side : BR2CameraLegSide)
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (certificate :
      CanonicalCompletedNativeBR2CenterLegCertificate
        camera radius hcamera hradius side xiState moments)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef :=
  hankelPair_posSemidef_of_completedNativeGreenFactors
    xiState moments hxi hnative certificate.toComplexMomentKernel N

end

end CarrySelfAdjointOperator

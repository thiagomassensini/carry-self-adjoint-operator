import CarrySelfAdjointOperator.AllBaseCenterLegNoDiagonal
import CarrySelfAdjointOperator.CompletedGreenMomentJets
import Mathlib.Tactic

/-!
# BR2 bipartite center--leg moment kernel

The coefficient matrix uses one center role and one bracket-leg role. Equality
of matrix indices therefore does not mean equality of geometric coordinates.
The all-base divisibility theorem proves something stronger: every center--leg
pair is geometrically off-diagonal, independently of the chosen index maps.

This file inserts that fact immediately before the already-audited
Green--Wronskian/Hankel bridge. A scalar Green kernel only needs an identity on
unequal geometric coordinates. The center--leg obstruction discharges that
side condition for every matrix entry, including entries with equal formal
indices, and produces the full complex Gram representation expected by
`CompletedGreenMomentJets`.

No primality hypothesis and no analytic diagonal regularization occur here.
The remaining BR2 work is the concrete off-diagonal scalarization of the
completed value/log-jet/provenance state.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- Which leg of a centered bracket is used by a bipartite readout. -/
inductive CameraLegSide where
  | left
  | right
  deriving DecidableEq

/-- Geometric coordinate of the selected bracket leg. -/
def cameraLegCoordinate
    (side : CameraLegSide) (base index radius : ℕ) : ℕ :=
  match side with
  | .left => cameraLeftLeg base index radius
  | .right => cameraRightLeg base index radius

/-- Arithmetic data assigning one aligned center and one admissible bracket
leg to every parity-jet index. The center and leg index maps may be different;
the no-diagonal theorem does not require them to agree. -/
structure BR2CameraIncidence where
  base : ℕ
  radius : ℕ
  hbase : IsSupported base
  hradius : radius ∈ radiusSet base
  side : CameraLegSide
  centerIndex : (ℕ ⊕ ℕ) → ℕ
  legIndex : (ℕ ⊕ ℕ) → ℕ

namespace BR2CameraIncidence

/-- Center coordinate assigned to a parity-jet index. -/
def centerCoordinate
    (incidence : BR2CameraIncidence) (i : ℕ ⊕ ℕ) : ℕ :=
  alignedCenter incidence.base (incidence.centerIndex i)

/-- Leg coordinate assigned to a parity-jet index. -/
def legCoordinate
    (incidence : BR2CameraIncidence) (j : ℕ ⊕ ℕ) : ℕ :=
  cameraLegCoordinate incidence.side incidence.base
    (incidence.legIndex j) incidence.radius

/-- Every center/leg pair selected by one supported camera lies off the
coordinate diagonal. This includes equal formal indices. -/
theorem centerCoordinate_ne_legCoordinate
    (incidence : BR2CameraIncidence) (i j : ℕ ⊕ ℕ) :
    incidence.centerCoordinate i ≠ incidence.legCoordinate j := by
  rcases incidence with
    ⟨base, radius, hbase, hradius, side, centerIndex, legIndex⟩
  cases side with
  | left =>
      simpa [centerCoordinate, legCoordinate, cameraLegCoordinate] using
        alignedCenter_ne_cameraLeftLeg
          hbase hradius (centerIndex i) (legIndex j)
  | right =>
      simpa [centerCoordinate, legCoordinate, cameraLegCoordinate] using
        alignedCenter_ne_cameraRightLeg
          hbase hradius (centerIndex i) (legIndex j)

/-- Same-index matrix entries remain geometrically off-diagonal. -/
theorem sameIndex_offDiagonal
    (incidence : BR2CameraIncidence) (i : ℕ ⊕ ℕ) :
    incidence.centerCoordinate i ≠ incidence.legCoordinate i :=
  incidence.centerCoordinate_ne_legCoordinate i i

end BR2CameraIncidence

/-- Natural-number label carried by a parity jet. -/
def parityJetNumber : (ℕ ⊕ ℕ) → ℕ
  | Sum.inl n => 2 * n
  | Sum.inr n => 2 * n + 1

/-- Canonical incidence using the parity-jet number on both roles. Equal
matrix indices still yield unequal geometric coordinates because the roles
are center and leg. -/
def canonicalParityCenterLegIncidence
    (base radius : ℕ)
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (side : CameraLegSide) : BR2CameraIncidence where
  base := base
  radius := radius
  hbase := hbase
  hradius := hradius
  side := side
  centerIndex := parityJetNumber
  legIndex := parityJetNumber

/-- Explicit same-index obstruction for the canonical parity incidence. -/
theorem canonicalParityCenterLeg_sameIndex_offDiagonal
    (base radius : ℕ)
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (side : CameraLegSide) (i : ℕ ⊕ ℕ) :
    (canonicalParityCenterLegIncidence
        base radius hbase hradius side).centerCoordinate i ≠
      (canonicalParityCenterLegIncidence
        base radius hbase hradius side).legCoordinate i :=
  (canonicalParityCenterLegIncidence
    base radius hbase hradius side).sameIndex_offDiagonal i

/-- A bipartite scalar Green kernel realizing the parity-split moment matrix.

`momentReadout` identifies the scalar kernel coefficients with the Hankel
moment kernel. `greenOffDiagonalReadout` identifies the same scalar values
with Hilbert inner products whenever the two geometric coordinates differ.
The camera incidence proves that this side condition holds for every entry. -/
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

/-- The all-base center--leg obstruction converts an off-diagonal Green
identity into the complete complex Gram representation, with no missing
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

/-- The certificate therefore makes both finite Hankel sections positive
semidefinite at every order. -/
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

/-- Concrete BR2 certificate type for the actual normalized completed
native/C3 product-ledger jets. -/
abbrev CanonicalCompletedNativeBR2CenterLegCertificate
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (base radius : ℕ)
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (side : CameraLegSide)
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ) :=
  BR2CenterLegGreenMomentCertificate
    (canonicalParityCenterLegIncidence
      base radius hbase hradius side)
    moments
    (completedGreenParityJet
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        (completedNativeC3ProductLedgerState xiState)))

/-- End-to-end finite positivity statement after the two factor Green
representations and the concrete center--leg coefficient certificate are
supplied. The former analytic diagonal premise has disappeared: all kernel
samples are geometrically off-diagonal by the camera divisibility theorem. -/
theorem hankelPair_posSemidef_of_canonicalCompletedNativeCenterLeg
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (base radius : ℕ)
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (side : CameraLegSide)
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (certificate :
      CanonicalCompletedNativeBR2CenterLegCertificate
        base radius hbase hradius side xiState moments)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef :=
  hankelPair_posSemidef_of_completedNativeGreenFactors
    xiState moments hxi hnative certificate.toComplexMomentKernel N

end

end CarrySelfAdjointOperator

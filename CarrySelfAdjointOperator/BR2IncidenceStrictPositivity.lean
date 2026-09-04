import CarrySelfAdjointOperator.AllBaseBracketIncidenceIndependence
import CarrySelfAdjointOperator.BR2CenterLegMomentKernel
import CarrySelfAdjointOperator.CanonicalFiniteHeight
import Mathlib.Tactic

/-!
# BR2 incidence transport to strict Hankel positivity

The center--leg no-go removes the false geometric diagonal and the bracket
incidence vectors are linearly independent by their unique center pivots.
This file records the exact remaining transport needed to turn that native
independence into strict positivity of the Green jets.

An injective real-linear map sends each even/odd bracket incidence to the
corresponding even/odd Green jet. Under that one transport certificate, the
already proved incidence independence becomes jet independence. Combined
with the BR2 center--leg Gram certificate, both Hankel sections become
positive definite and the canonical finite height operator is symmetric.

No claim is made here that the concrete completed C3/TFVD state already
supplies the transport. The point is to reduce strictness to one typed,
lossless state-identification theorem instead of an external positivity
assumption.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- Lossless transport from native bracket-incidence vectors to a parity-jet
family. Injectivity forbids the state readout from collapsing a nonzero
incidence combination. -/
structure BR2BracketIncidenceJetTransport
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (base radius : ℕ) (jet : (ℕ ⊕ ℕ) → E) where
  toLinearMap : (ℕ →₀ ℝ) →ₗ[ℝ] E
  injective : Function.Injective toLinearMap
  even_eq : ∀ n : ℕ,
    jet (Sum.inl n) =
      toLinearMap (cameraBracketIncidence base radius (2 * n))
  odd_eq : ∀ n : ℕ,
    jet (Sum.inr n) =
      toLinearMap (cameraBracketIncidence base radius (2 * n + 1))

namespace BR2BracketIncidenceJetTransport

/-- The even jet prefix inherits native bracket-incidence independence. -/
theorem evenPrefix_linearIndependent
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {base radius : ℕ} {jet : (ℕ ⊕ ℕ) → E}
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (N : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin N => jet (Sum.inl (i : ℕ))) := by
  have hsource :=
    evenCameraBracketIncidence_linearIndependent hbase hradius N
  have hmapped :
      LinearIndependent ℝ
        (transport.toLinearMap ∘
          (fun i : Fin N =>
            cameraBracketIncidence base radius (2 * (i : ℕ)))) :=
    hsource.map_injOn transport.toLinearMap transport.injective.injOn
  have hfamily :
      (fun i : Fin N => jet (Sum.inl (i : ℕ))) =
        transport.toLinearMap ∘
          (fun i : Fin N =>
            cameraBracketIncidence base radius (2 * (i : ℕ))) := by
    funext i
    exact transport.even_eq (i : ℕ)
  rw [hfamily]
  exact hmapped

/-- The odd jet prefix inherits native bracket-incidence independence. -/
theorem oddPrefix_linearIndependent
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {base radius : ℕ} {jet : (ℕ ⊕ ℕ) → E}
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (N : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin N => jet (Sum.inr (i : ℕ))) := by
  have hsource :=
    oddCameraBracketIncidence_linearIndependent hbase hradius N
  have hmapped :
      LinearIndependent ℝ
        (transport.toLinearMap ∘
          (fun i : Fin N =>
            cameraBracketIncidence base radius (2 * (i : ℕ) + 1))) :=
    hsource.map_injOn transport.toLinearMap transport.injective.injOn
  have hfamily :
      (fun i : Fin N => jet (Sum.inr (i : ℕ))) =
        transport.toLinearMap ∘
          (fun i : Fin N =>
            cameraBracketIncidence base radius (2 * (i : ℕ) + 1)) := by
    funext i
    exact transport.odd_eq (i : ℕ)
  rw [hfamily]
  exact hmapped

/-- The complete even jet family inherits independence from every finite
native bracket-incidence subfamily. -/
theorem even_linearIndependent
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {base radius : ℕ} {jet : (ℕ ⊕ ℕ) → E}
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have hindex : Function.Injective (fun i : s => 2 * (i : ℕ)) := by
    intro i j hij
    dsimp only at hij
    apply Subtype.ext
    omega
  have hsource := cameraBracketIncidence_linearIndependent_of_injective
    hbase hradius (fun i : s => 2 * (i : ℕ)) hindex
  have hmapped := hsource.map_injOn
    transport.toLinearMap transport.injective.injOn
  have hfamily :
      (fun n : ℕ => jet (Sum.inl n)) ∘ (Subtype.val : s → ℕ) =
        transport.toLinearMap ∘
          (fun i : s => cameraBracketIncidence base radius (2 * (i : ℕ))) := by
    funext i
    exact transport.even_eq (i : ℕ)
  rw [hfamily]
  exact hmapped

/-- The complete odd jet family inherits independence from every finite
native bracket-incidence subfamily. -/
theorem odd_linearIndependent
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {base radius : ℕ} {jet : (ℕ ⊕ ℕ) → E}
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have hindex : Function.Injective (fun i : s => 2 * (i : ℕ) + 1) := by
    intro i j hij
    dsimp only at hij
    apply Subtype.ext
    omega
  have hsource := cameraBracketIncidence_linearIndependent_of_injective
    hbase hradius (fun i : s => 2 * (i : ℕ) + 1) hindex
  have hmapped := hsource.map_injOn
    transport.toLinearMap transport.injective.injOn
  have hfamily :
      (fun n : ℕ => jet (Sum.inr n)) ∘ (Subtype.val : s → ℕ) =
        transport.toLinearMap ∘
          (fun i : s => cameraBracketIncidence base radius (2 * (i : ℕ) + 1)) := by
    funext i
    exact transport.odd_eq (i : ℕ)
  rw [hfamily]
  exact hmapped

end BR2BracketIncidenceJetTransport

section ComplexRealification

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local instance : InnerProductSpace ℝ E :=
  InnerProductSpace.rclikeToReal ℂ E

/-- The complex BR2 center--leg certificate supplies the real Gram kernel
needed by the strict-positivity theorem. -/
theorem BR2CenterLegGreenMomentCertificate.toRealMomentKernel
    {incidence : BR2CameraIncidence}
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (certificate :
      BR2CenterLegGreenMomentCertificate incidence moments jet) :
    IsGreenWronskianMomentKernelGramRepresentation moments jet := by
  intro i j
  change greenWronskianMomentKernel moments i j =
    (inner ℂ (jet i) (jet j)).re
  have h := congrArg Complex.re
    (certificate.toComplexMomentKernel i j)
  simpa using h

/-- Native incidence transport upgrades the BR2 Gram certificate from
semidefinite to positive definite at every finite order. -/
theorem BR2CenterLegGreenMomentCertificate.hankelPair_posDef_of_incidenceTransport
    {incidence : BR2CameraIncidence}
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (certificate :
      BR2CenterLegGreenMomentCertificate incidence moments jet)
    (transport :
      BR2BracketIncidenceJetTransport
        incidence.base incidence.radius jet)
    (N : ℕ) :
    (hankelGram moments N).PosDef ∧
      (shiftedHankel moments N).PosDef := by
  exact hankelPair_posDef_of_greenWronskianMomentKernel
    certificate.toRealMomentKernel N
    (transport.evenPrefix_linearIndependent
      incidence.hbase incidence.hradius N)
    (transport.oddPrefix_linearIndependent
      incidence.hbase incidence.hradius N)

/-- Under the same transport, the canonical finite height operator generated
from the moments has an exact symmetry certificate. The existentially
packaged proof arguments are the canonical Hankel positivity and odd-jet
independence certificates constructed above. -/
theorem BR2CenterLegGreenMomentCertificate.exists_canonicalFiniteHeightOperator_isSymm_of_incidenceTransport
    {incidence : BR2CameraIncidence}
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (certificate :
      BR2CenterLegGreenMomentCertificate incidence moments jet)
    (transport :
      BR2BracketIncidenceJetTransport
        incidence.base incidence.radius jet)
    (N : ℕ) :
    ∃ (hgram : (hankelGram moments N).PosDef)
      (hodd : LinearIndependent ℝ
        (fun i : Fin N => jet (Sum.inr (i : ℕ)))),
      (canonicalFiniteHeightOperator
        (greenWronskianMomentKernel_odd_shiftedMomentGram
          certificate.toRealMomentKernel)
        N hgram hodd).IsSymm := by
  let hodd := transport.oddPrefix_linearIndependent
    incidence.hbase incidence.hradius N
  let hpos := certificate.hankelPair_posDef_of_incidenceTransport
    transport N
  refine ⟨hpos.1, hodd, ?_⟩
  exact canonicalFiniteHeightOperator_isSymm
    (greenWronskianMomentKernel_odd_shiftedMomentGram
      certificate.toRealMomentKernel)
    N hpos.1 hodd

end ComplexRealification

/-- Concrete transport type for the actual normalized completed native/C3
parity jets. -/
abbrev CanonicalCompletedNativeBR2IncidenceJetTransport
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (base radius : ℕ) (xiState : ℂ → Hxi) :=
  BR2BracketIncidenceJetTransport base radius
    (completedGreenParityJet
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        (completedNativeC3ProductLedgerState xiState)))

end

end CarrySelfAdjointOperator

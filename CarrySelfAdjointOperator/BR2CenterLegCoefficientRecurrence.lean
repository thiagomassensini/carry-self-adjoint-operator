import CarrySelfAdjointOperator.BR2CenterLegMomentKernel
import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import Mathlib.Tactic

/-!
# BR2 center--leg coefficient recurrence

The all-order division-free coefficient recurrence already determines the
parity-split moment value of every coefficient. The all-base center--leg
lattice theorem supplies the complementary geometric fact: every coefficient
readout is evaluated away from the coordinate diagonal, even when its two
formal matrix indices agree.

Thus the remaining state-level input is one off-diagonal Green readout of the
coefficient array. No separate matrix-diagonal value, preassembled Gram
representation, or primality hypothesis is accepted by this interface.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Sharper BR2 certificate: the scalar coefficient array already satisfies
the all-order division-free recurrence. The only remaining state-level input
is its Green readout on center--leg pairs. Lattice separation discharges the
off-diagonal side condition for every parity entry. -/
structure BR2CenterLegCoefficientCertificate
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (incidence : BR2CameraIncidence)
    (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → E) where
  coeff : ℕ → ℕ → ℂ
  coefficientEquation :
    IsPolarizedGreenCoefficientEquation moments coeff
  greenOffDiagonalReadout : ∀ i j : ℕ ⊕ ℕ,
    incidence.centerCoordinate i ≠ incidence.legCoordinate j →
      coeff (br2ParityJetNumber i) (br2ParityJetNumber j) =
        inner ℂ (jet i) (jet j)

namespace BR2CenterLegCoefficientCertificate

/-- The recurrence fixes the moment value of every parity coefficient, while
the all-base center--leg theorem makes its Green readout available at every
entry. -/
theorem toComplexMomentKernel
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {incidence : BR2CameraIncidence}
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (certificate :
      BR2CenterLegCoefficientCertificate incidence moments jet) :
    IsComplexGreenWronskianMomentKernelGramRepresentation moments jet := by
  intro i j
  have hgreen := certificate.greenOffDiagonalReadout i j
    (incidence.centerCoordinate_ne_legCoordinate i j)
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have hcoeff := polarizedGreenCoefficient_unique
            certificate.coefficientEquation (2 * i) (2 * j)
          calc
            (greenWronskianMomentKernel moments
                (Sum.inl i) (Sum.inl j) : ℂ) =
              certificate.coeff (2 * i) (2 * j) := by
                simpa [greenWronskianMomentKernel] using hcoeff.symm
            _ = inner ℂ (jet (Sum.inl i)) (jet (Sum.inl j)) := by
              simpa [br2ParityJetNumber] using hgreen
      | inr j =>
          have hcoeff := polarizedGreenCoefficient_unique
            certificate.coefficientEquation (2 * i) (2 * j + 1)
          calc
            (greenWronskianMomentKernel moments
                (Sum.inl i) (Sum.inr j) : ℂ) =
              certificate.coeff (2 * i) (2 * j + 1) := by
                simpa [greenWronskianMomentKernel] using hcoeff.symm
            _ = inner ℂ (jet (Sum.inl i)) (jet (Sum.inr j)) := by
              simpa [br2ParityJetNumber] using hgreen
  | inr i =>
      cases j with
      | inl j =>
          have hcoeff := polarizedGreenCoefficient_unique
            certificate.coefficientEquation (2 * i + 1) (2 * j)
          calc
            (greenWronskianMomentKernel moments
                (Sum.inr i) (Sum.inl j) : ℂ) =
              certificate.coeff (2 * i + 1) (2 * j) := by
                simpa [greenWronskianMomentKernel] using hcoeff.symm
            _ = inner ℂ (jet (Sum.inr i)) (jet (Sum.inl j)) := by
              simpa [br2ParityJetNumber] using hgreen
      | inr j =>
          have hcoeff := polarizedGreenCoefficient_unique
            certificate.coefficientEquation (2 * i + 1) (2 * j + 1)
          calc
            (greenWronskianMomentKernel moments
                (Sum.inr i) (Sum.inr j) : ℂ) =
              certificate.coeff (2 * i + 1) (2 * j + 1) := by
                simpa [greenWronskianMomentKernel] using hcoeff.symm
            _ = inner ℂ (jet (Sum.inr i)) (jet (Sum.inr j)) := by
              simpa [br2ParityJetNumber] using hgreen

/-- Finite Hankel positivity follows from one off-diagonal Green readout plus
the already-proved all-order coefficient recurrence. -/
theorem hankelPair_posSemidef
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {incidence : BR2CameraIncidence}
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (certificate :
      BR2CenterLegCoefficientCertificate incidence moments jet)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef :=
  hankelPair_posSemidef_of_complexGreenWronskianMomentKernel
    certificate.toComplexMomentKernel N

end BR2CenterLegCoefficientCertificate

end

end CarrySelfAdjointOperator

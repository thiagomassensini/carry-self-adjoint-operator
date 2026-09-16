import CarrySelfAdjointOperator.FiveFieldCapstoneMinimal

/-!
Jet-level consequences of the differential systems recorded in the final
five-field notes.  The file does not assert that a physical field exists; it
formalizes only the algebra that follows once the corresponding jet equations
are supplied.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

structure MixedGreenSecondJet where
  c : ℂ
  cDelta : ℂ
  cDeltaDelta : ℂ
  source : ℂ
  equation : cDeltaDelta - (1 / 4 : ℂ) * c = source

def mixedYplus (j : MixedGreenSecondJet) : ℂ :=
  j.c + 2 * j.cDelta

def mixedYminus (j : MixedGreenSecondJet) : ℂ :=
  j.c - 2 * j.cDelta

theorem mixedYplus_transport (j : MixedGreenSecondJet) :
    (j.cDelta + 2 * j.cDeltaDelta) -
        (1 / 2 : ℂ) * mixedYplus j =
      2 * j.source := by
  rw [← j.equation]
  simp [mixedYplus]
  ring

theorem mixedYminus_transport (j : MixedGreenSecondJet) :
    (j.cDelta - 2 * j.cDeltaDelta) +
        (1 / 2 : ℂ) * mixedYminus j =
      -2 * j.source := by
  rw [← j.equation]
  simp [mixedYminus]
  ring

structure SingleJumpChannelJet where
  t : ℂ
  c : ℂ
  x : ℂ
  cPrime : ℂ
  xPrime : ℂ
  endpoint : ℂ
  boundary : ℂ
  cEquation : cPrime = -c - x / t + endpoint / t
  xEquation : xPrime = x / t - endpoint / t + 2 * boundary

theorem singleJump_sum_transport (j : SingleJumpChannelJet) :
    j.cPrime + j.xPrime = -j.c + 2 * j.boundary := by
  rw [j.cEquation, j.xEquation]
  ring

theorem singleJump_equations_weighted
    (j : SingleJumpChannelJet) (ht : j.t ≠ 0) :
    j.t * j.cPrime = -j.t * j.c - j.x + j.endpoint ∧
      j.t * j.xPrime = j.x - j.endpoint + 2 * j.t * j.boundary := by
  constructor
  · rw [j.cEquation]
    field_simp
  · rw [j.xEquation]
    field_simp

end
end NativeCarryFiveFieldCapstone

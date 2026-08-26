import CarrySelfAdjointOperator.NativeScalarGenuineIdentification
import CPFormal.Analytic.CpGenuineReflectionRigidity
import Mathlib.Tactic

/-!
# Carry-native Schwarz reflection

The paired carry channel conjugates term by term.  Its nonvanishing eta-type
factor can therefore be cancelled on the Genuine strip, yielding Schwarz
reflection for the canonical Genuine continuation and hence for the native
scalar.  No classical comparison is used.

This is the conjugation symmetry `s ↦ conj s`; it is not the centered
reflection `s ↦ 1 - s`.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Schwarz reflection of the canonical Genuine continuation, obtained from
the termwise-conjugating paired carry channel. -/
theorem genuineContinuation_conj_native
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineContinuation ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (genuineContinuation s) := by
  have hsconj := conj_mem_genuineCriticalStrip hs
  have harg : ((2 : ℂ)).arg ≠ Real.pi := by
    rw [← Complex.ofReal_ofNat]
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  have hexponent :
      (1 : ℂ) - (starRingEnd ℂ) s =
        (starRingEnd ℂ) ((1 : ℂ) - s) := by simp
  have hfactor :
      (1 : ℂ) - (2 : ℂ) ^ (1 - (starRingEnd ℂ) s) =
        (starRingEnd ℂ) ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) := by
    rw [hexponent, Complex.cpow_conj _ _ harg, map_ofNat]
    simp only [map_sub, map_one]
  have hleft := pairedAltChannel_eq_genuineContinuation hsconj
  have hright := pairedAltChannel_eq_genuineContinuation hs
  apply mul_left_cancel₀ (one_sub_two_cpow_one_sub_ne_zero hsconj)
  calc
    ((1 : ℂ) - (2 : ℂ) ^ (1 - (starRingEnd ℂ) s)) *
          genuineContinuation ((starRingEnd ℂ) s) =
        pairedAltChannel ((starRingEnd ℂ) s) := hleft.symm
    _ = (starRingEnd ℂ) (pairedAltChannel s) := pairedAltChannel_conj s
    _ = (starRingEnd ℂ)
          (((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * genuineContinuation s) := by
        rw [hright]
    _ = ((1 : ℂ) - (2 : ℂ) ^ (1 - (starRingEnd ℂ) s)) *
          (starRingEnd ℂ) (genuineContinuation s) := by
        rw [map_mul, ← hfactor]

/-- Schwarz reflection transported to the carry-native scalar. -/
theorem nativeScalar_conj_native
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    nativeScalar ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (nativeScalar s) := by
  rw [nativeScalar_eq_genuineContinuation_unconditional,
    nativeScalar_eq_genuineContinuation_unconditional,
    genuineContinuation_conj_native hs]

end

end CarrySelfAdjointOperator

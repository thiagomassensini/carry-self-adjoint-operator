import CarrySelfAdjointOperator.CanonicalEnrichedC3Port
import NativeCarryC3Crosswalk.GenuineBracketGreenFactorization

/-!
# Concrete canonical C3 Green intertwiner

The canonical enriched source port is not an abstract Hilbert-space witness:
it is literally the already formalized camera-3 Genuine Green boundary pair
at the first complete block.  Consequently its direct/reflected Green bulk
inherits the exact radial factorization and has no zero in the open strip
away from `re s = 1/2`.

This isolates the final scalar-to-state statement without replacing the
reflected C3 form by an unrelated norm square.  The sole remaining equation
identifies the diagonal Wronskian of the completed native characteristic with
this exact provenance-preserving C3 Green bulk.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The minimal canonical enriched port is exactly the existing complete
camera-3 Genuine Green boundary pair. -/
theorem canonicalEnrichedC3SourcePort_eq_greenBoundaryPair (s : ℂ) :
    canonicalEnrichedC3SourcePort s =
      NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s := by
  unfold canonicalEnrichedC3SourcePort
  change
    NativeCarryC3Crosswalk.finiteC3EnrichedTfvdValueGreenPort
        1 (1 : ℂ) (fun _ : ℕ ↦ (1 : ℂ)) s
          (canonicalSeededEnrichedTfvdGenuinePort
            (1 : ℂ) (fun _ : ℕ ↦ (1 : ℂ)) s) =
      NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 s
  simpa using
    (NativeCarryC3Crosswalk.finiteC3EnrichedTfvdValueGreenPort_canonical
      1 (by norm_num : (1 : ℂ) ≠ 0)
      (fun _ : ℕ ↦ (1 : ℂ)) (by intro m; norm_num) s)

/-- Direct/reflected Green bulk of the exact canonical enriched C3 state. -/
def canonicalEnrichedC3ReflectedGreenBulk (s : ℂ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (canonicalEnrichedC3SourcePort s)
    (canonicalEnrichedC3SourcePort (reflectedParameter s))

/-- The canonical C3 bulk inherits the exact radial factorization. -/
theorem canonicalEnrichedC3ReflectedGreenBulk_eq_radialFactorization
    (s : ℂ) :
    canonicalEnrichedC3ReflectedGreenBulk s =
      ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteReflectedGradientPairing 3 s := by
  unfold canonicalEnrichedC3ReflectedGreenBulk
  rw [canonicalEnrichedC3SourcePort_eq_greenBoundaryPair,
    canonicalEnrichedC3SourcePort_eq_greenBoundaryPair]
  exact
    NativeCarryC3Crosswalk.greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization
      3 s

/-- In the open strip, this concrete finite C3 bulk vanishes exactly on the
critical line.  Its reflected pairing is already known to be nonzero. -/
theorem canonicalEnrichedC3ReflectedGreenBulk_eq_zero_iff_re_eq_half
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalEnrichedC3ReflectedGreenBulk s = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [canonicalEnrichedC3ReflectedGreenBulk_eq_radialFactorization]
  constructor
  · intro hzero
    have hpair : finiteReflectedGradientPairing 3 s ≠ 0 :=
      finiteReflectedGradientPairing_ne_zero (by norm_num) hs
    have hradialComplex :
        ((cpRadialDifference 3
          (criticalDisplacement s.re) : ℝ) : ℂ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hpair
    have hradial :
        cpRadialDifference 3 (criticalDisplacement s.re) = 0 := by
      exact_mod_cast hradialComplex
    have hcritical : criticalDisplacement s.re = 0 :=
      (cpRadialDifference_eq_zero_iff
        3 (by norm_num) (criticalDisplacement s.re)).1 hradial
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    have hcritical : criticalDisplacement s.re = 0 := by
      unfold criticalDisplacement
      linarith
    rw [hcritical]
    simp [cpRadialDifference]

/-- Exact final intertwiner obligation.  It compares two concrete objects:
the canonical diagonal Wronskian of the completed native characteristic and
the direct/reflected Green bulk of the canonical enriched C3 port. -/
def HasCanonicalEnrichedC3DiagonalGreenIntertwiner : Prop :=
  ∀ z : ℂ, z.im ≠ 0 →
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z =
      canonicalEnrichedC3ReflectedGreenBulk
        (operatorHeightParameter z)

/-- With the exact canonical C3 intertwiner, every open-strip zeta zero is
on the critical line.  Nonvanishing of the finite reflected Green pairing is
discharged internally; no separate state hypothesis remains. -/
theorem riemannZeta_zero_re_eq_half_of_canonicalEnrichedC3Intertwiner
    (hintertwiner : HasCanonicalEnrichedC3DiagonalGreenIntertwiner)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0) :
    s.re = 1 / 2 := by
  by_contra hre
  have hzIm : (centeredHeightParameter s).im ≠ 0 := by
    rw [centeredHeightParameter_im]
    intro h
    apply hre
    linarith
  have hcharacteristic :
      completedNativeOperatorCharacteristic
          (centeredHeightParameter s) = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta]
    · simp [hzero]
    · simpa using hs
  have hwronskian :
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion
          (centeredHeightParameter s) (centeredHeightParameter s) = 0 := by
    simp [completedGreenWronskian, hcharacteristic]
  have hintertwinerAt := hintertwiner (centeredHeightParameter s) hzIm
  rw [hwronskian] at hintertwinerAt
  have hbulk : canonicalEnrichedC3ReflectedGreenBulk s = 0 := by
    simpa using hintertwinerAt.symm
  exact hre
    ((canonicalEnrichedC3ReflectedGreenBulk_eq_zero_iff_re_eq_half hs).1
      hbulk)

end

end CarrySelfAdjointOperator

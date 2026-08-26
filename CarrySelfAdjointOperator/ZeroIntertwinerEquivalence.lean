import CarrySelfAdjointOperator.NativeScalarZetaIdentification
import CarrySelfAdjointOperator.CanonicalC3GreenIntertwiner

/-!
# Exact status of the zero-localized scalar intertwiner

At a zeta zero, the completed scalar diagonal Wronskian is already zero by
the exact product-jet decomposition.  The canonical enriched C3 Green bulk,
on the other hand, vanishes in the open strip exactly on the critical line.

This file therefore proves, in the kernel, that asking only for equality of
those two scalar quantities at zeta zeros is equivalent to the desired
critical-line conclusion.  It is not an independent route to that conclusion.
Any noncircular completion must construct the intertwiner before scalar
projection (retaining provenance/mixed channels), or supply the independent
infinite Jacobi/Weyl realization.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The weakest zero-localized version of the proposed scalar C3
intertwiner.  It asks for equality only at zeta zeros in the open strip. -/
def HasCanonicalEnrichedC3ZeroDiagonalGreenIntertwiner : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip → riemannZeta s = 0 →
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion
        (centeredHeightParameter s) (centeredHeightParameter s) =
      canonicalEnrichedC3ReflectedGreenBulk s

/-- Kernel-level diagnosis of the remaining scalar seam: the zero-localized
scalar intertwiner is logically equivalent to critical-line confinement for
open-strip zeta zeros. -/
theorem canonicalEnrichedC3ZeroDiagonalGreenIntertwiner_iff_confinement :
    HasCanonicalEnrichedC3ZeroDiagonalGreenIntertwiner ↔
      ∀ {s : ℂ}, s ∈ genuineCriticalStrip → riemannZeta s = 0 →
        s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hintertwiner s hs hzero
    apply (canonicalEnrichedC3ReflectedGreenBulk_eq_zero_iff_re_eq_half hs).1
    have hscalar :
        completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion
            (centeredHeightParameter s) (centeredHeightParameter s) = 0 := by
      apply completedNativeOperatorGreenWronskian_eq_zero_at_riemannZeta_zero
      · simpa using hs
      · simpa using hzero
    have hseam := hintertwiner hs hzero
    rw [hscalar] at hseam
    exact hseam.symm
  · intro hconfinement s hs hzero
    have hscalar :
        completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion
            (centeredHeightParameter s) (centeredHeightParameter s) = 0 := by
      apply completedNativeOperatorGreenWronskian_eq_zero_at_riemannZeta_zero
      · simpa using hs
      · simpa using hzero
    have hbulk : canonicalEnrichedC3ReflectedGreenBulk s = 0 :=
      (canonicalEnrichedC3ReflectedGreenBulk_eq_zero_iff_re_eq_half hs).2
        (hconfinement hs hzero)
    exact hscalar.trans hbulk.symm

end

end CarrySelfAdjointOperator

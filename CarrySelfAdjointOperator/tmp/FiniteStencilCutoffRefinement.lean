import NativeCarrySpectralWeyl.Camera.FiniteCoefficientBridge

/-!
# Exact cutoff refinement of the formal native camera stencil

Splitting a cutoff `M + N` at `M` gives the old stencil plus the exact block
of the next `N` aligned centers.  At `N = M` this is the algebraic doubling
law used by the enriched-camera limit audit.  The statement lives in the
free integer stencil module, before evaluation at any time or state.
-/

open scoped BigOperators

namespace NativeCarrySpectralWeyl.Camera.FiniteBridge

noncomputable section

/-- Formal block of `length` consecutive camera cells beginning at
`start`. -/
def centerStencilBlock (camera start length : ℕ) : FormalStencil :=
  ∑ index ∈ Finset.range length, centerStencil camera (start + index)

/-- Exact additive refinement of the finite stencil at an arbitrary cutoff
split. -/
theorem finiteStencil_add_cutoff (camera cutoff length : ℕ) :
    finiteStencil camera (cutoff + length) =
      finiteStencil camera cutoff +
        centerStencilBlock camera cutoff length := by
  unfold finiteStencil centerStencilBlock
  rw [Finset.sum_range_add]
  abel

/-- Exact dyadic refinement: the `2M` stencil is the `M` stencil plus the
next block of `M` native cells. -/
theorem finiteStencil_double (camera cutoff : ℕ) :
    finiteStencil camera (cutoff + cutoff) =
      finiteStencil camera cutoff +
        centerStencilBlock camera cutoff cutoff :=
  finiteStencil_add_cutoff camera cutoff cutoff

/-- Coefficientwise form of exact dyadic refinement. -/
theorem finiteCoefficient_double (camera cutoff position : ℕ) :
    finiteCoefficient camera (cutoff + cutoff) position =
      finiteCoefficient camera cutoff position +
        centerStencilBlock camera cutoff cutoff position := by
  simpa only [finiteStencil_apply, Finsupp.add_apply] using
    congrArg (fun stencil : FormalStencil => stencil position)
      (finiteStencil_double camera cutoff)

end

end NativeCarrySpectralWeyl.Camera.FiniteBridge

#print axioms NativeCarrySpectralWeyl.Camera.FiniteBridge.finiteStencil_double
#print axioms NativeCarrySpectralWeyl.Camera.FiniteBridge.finiteCoefficient_double

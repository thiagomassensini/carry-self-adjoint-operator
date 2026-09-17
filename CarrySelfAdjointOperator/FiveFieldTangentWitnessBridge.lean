import CarrySelfAdjointOperator.FiveFieldTangentTailReadout
import Mathlib.Tactic

/-!
# Laurent witness bridge for the concrete tangent reconstruction

The effective variational Riemann--Hilbert calculation supplies three
Laurent coefficients. This file records the exact minimum interface between
those coefficients and the reconstruction from the previous checkpoints.
It is deliberately a witness theorem: it does not identify an arbitrary
matrix-valued moment function with the physical `state_at_n` family.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

open scoped Matrix.Norms.Elementwise

/-- If the three Laurent coefficients of an effective tangent agree with the
coefficients computed from the Cauchy moments, the explicit reconstruction
recovers that effective tangent exactly. -/
theorem twoJumpTangentResiduesLinear_eq_of_laurent_moments
    (κ t1 t2 : ℂ) (h1 : t1 ≠ 0) (h2 : t2 ≠ 0) (h12 : t2 ≠ t1)
    (A H dA : Fin 3 → TwoByTwo)
    (hLaurent : twoJumpResidueMoments t1 t2 dA =
      twoJumpTangentLaurentCoefficients κ t1 t2 A H) :
    twoJumpTangentResiduesLinear κ t1 t2 A H = dA := by
  change twoJumpReconstructResidues t1 t2
      (twoJumpTangentLaurentCoefficients κ t1 t2 A H) = dA
  rw [← hLaurent]
  exact twoJumpReconstructResidues_moments t1 t2 h1 h2 h12 dA

/-- The same witness bridge after applying the native four-coordinate
readout. -/
theorem twoJumpScalarFromMoments_eq_effective_readout
    (κ t1 t2 : ℂ) (h1 : t1 ≠ 0) (h2 : t2 ≠ 0) (h12 : t2 ≠ t1)
    (A H dA : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ)
    (hLaurent : twoJumpResidueMoments t1 t2 dA =
      twoJumpTangentLaurentCoefficients κ t1 t2 A H) :
    twoJumpScalarFromMoments κ t1 t2 A u H =
      twoJumpRadialPairingLinear u (twoJumpResidueCoordinateLinear A dA) := by
  change twoJumpRadialPairingLinear u
      (twoJumpResidueCoordinateLinear A
        (twoJumpTangentResiduesLinear κ t1 t2 A H)) = _
  rw [twoJumpTangentResiduesLinear_eq_of_laurent_moments
    κ t1 t2 h1 h2 h12 A H dA hLaurent]

/-- A form useful when the effective tangent is already presented through its
four native coordinates. -/
theorem twoJumpScalarFromMoments_eq_effective_coordinate_pairing
    (κ t1 t2 : ℂ) (h1 : t1 ≠ 0) (h2 : t2 ≠ 0) (h12 : t2 ≠ t1)
    (A H dA : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ)
    (v : Fin 4 → ℂ)
    (hLaurent : twoJumpResidueMoments t1 t2 dA =
      twoJumpTangentLaurentCoefficients κ t1 t2 A H)
    (hv : twoJumpResidueCoordinateLinear A dA = v) :
    twoJumpScalarFromMoments κ t1 t2 A u H =
      twoJumpRadialPairingLinear u v := by
  rw [twoJumpScalarFromMoments_eq_effective_readout
    κ t1 t2 h1 h2 h12 A H dA u hLaurent, hv]

end

end NativeCarryFiveFieldCapstone

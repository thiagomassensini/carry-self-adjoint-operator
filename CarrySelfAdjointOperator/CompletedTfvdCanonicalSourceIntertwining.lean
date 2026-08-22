import CarrySelfAdjointOperator.CanonicalC3SixCameraSource
import NativeCarryC3Crosswalk.CompletedTfvdGreenIntertwining

/-!
# Canonical completed TFVD source intertwining

The public C3 crosswalk now reconstructs the complete three-cell Green port
from the uncollapsed ordinary/log-jet ledger and packs it faithfully into six
all-bases cameras.  This file proves that the completed-operator repository's
previously constructed canonical C3 port and six-camera source are literally
those same objects.

No new source, scalarization equation, zero hypothesis, or selected inverse is
introduced.  The purpose is to remove duplicate canonical carriers before the
remaining completed Wronskian/Cauchy scalarization is addressed.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The private enriched cutoff-one C3 port is exactly the complete C3 port
reconstructed from the public uncollapsed TFVD ledger. -/
theorem canonicalEnrichedC3SourcePort_eq_completedTfvdGreenLedgerC3Port
    (s : ℂ) :
    canonicalEnrichedC3SourcePort s =
      NativeCarryC3Crosswalk.completedTfvdGreenLedgerC3Port s
        (NativeCarryC3Crosswalk.seededCompletedTfvdGreenLedger 1 s) := by
  rw [NativeCarryC3Crosswalk.completedTfvdGreenLedgerC3Port_seeded]
  unfold canonicalEnrichedC3SourcePort
  simpa using
    (NativeCarryC3Crosswalk.finiteC3EnrichedTfvdPairTransport_canonical
      1 (kappa := (1 : ℂ)) (by norm_num)
      (fun _ : ℕ => (1 : ℂ)) (by intro m; norm_num) s).2.2

/-- The duplicated real camera channel is definitionally the public faithful
C3 camera channel. -/
theorem canonicalC3RealCameraFinsupp_eq_public
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    canonicalC3RealCameraFinsupp x =
      NativeCarryC3Crosswalk.c3RealCameraFinsupp x := by
  rfl

/-- The duplicated imaginary camera channel is definitionally the public
faithful C3 camera channel. -/
theorem canonicalC3ImagCameraFinsupp_eq_public
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    canonicalC3ImagCameraFinsupp x =
      NativeCarryC3Crosswalk.c3ImagCameraFinsupp x := by
  rfl

/-- The private six-camera source map is the public bounded faithful packing. -/
theorem canonicalC3SixCameraSourceMap_eq_publicPacking
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    canonicalC3SixCameraSourceMap x =
      NativeCarryC3Crosswalk.c3SixCameraPacking x := by
  rw [NativeCarryC3Crosswalk.c3SixCameraPacking_apply]
  simp only [canonicalC3SixCameraSourceMap,
    canonicalC3RealCameraFinsupp_eq_public,
    canonicalC3ImagCameraFinsupp_eq_public]

/-- The canonical completed-operator source at height `z` is exactly the
public six-camera state reconstructed from the completed TFVD ledger at the
corresponding spectral parameter. -/
theorem canonicalCompletedC3SixCameraSource_eq_completedTfvdGreenCameraState
    (z : ℂ) :
    canonicalCompletedC3SixCameraSource z =
      NativeCarryC3Crosswalk.seededCompletedTfvdGreenCameraState
        (operatorHeightParameter z) := by
  unfold canonicalCompletedC3SixCameraSource
    canonicalCompletedOperatorC3State
  rw [canonicalC3SixCameraSourceMap_eq_publicPacking,
    canonicalEnrichedC3SourcePort_eq_completedTfvdGreenLedgerC3Port]
  rfl

/-- The intrinsic complex carry-time coordinate is exactly the centered height
coordinate already used by the self-adjoint operator. -/
@[simp] theorem carryComplexTimeOfParameter_eq_centeredHeightParameter
    (s : ℂ) :
    carryComplexTimeOfParameter s = centeredHeightParameter s := by
  apply Complex.ext <;>
    simp [carryComplexTimeOfParameter, centeredHeightParameter,
      criticalDisplacement]

/-- Centering a strip parameter in the private source recovers literally the
public ledger-derived camera state at that parameter. -/
@[simp] theorem canonicalCompletedC3SixCameraSource_centeredHeightParameter
    (s : ℂ) :
    canonicalCompletedC3SixCameraSource (centeredHeightParameter s) =
      NativeCarryC3Crosswalk.seededCompletedTfvdGreenCameraState s := by
  rw [canonicalCompletedC3SixCameraSource_eq_completedTfvdGreenCameraState]
  simp

end

end CarrySelfAdjointOperator

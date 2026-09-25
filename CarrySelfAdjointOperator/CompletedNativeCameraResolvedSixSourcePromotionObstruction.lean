import CarrySelfAdjointOperator.MultibaseCameraLogTfvdChannelTransport
import CarrySelfAdjointOperator.CompletedNativeSeededClockTfvdSixSource
import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceCameraPromotionAudit
import Mathlib.Tactic

/-!
# Obstruction to reusing the log-camera resolver for the ordinary six-source role

The existing camera-resolved channel is a resolution of the *logarithmic*
Dirichlet value.  It cannot simply be reused as a resolution of the ordinary
Dirichlet source: at the initial vertex, the factorization camera ledger is
zero (`log 1 = 0`), whereas the ordinary Dirichlet value is the nonzero
boundary seed `1`.

This is deliberately a local obstruction.  It does not rule out a future
six-role promotion carrying an additional boundary/incoming channel.  It does
show that the currently available log-camera family cannot by itself furnish
the ordinary role at `z`, `w`, or reflected `z`.
-/

open scoped ComplexConjugate InnerProductSpace BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The actual parameter carried by each of the three six-source parameter
roles.  This only exposes the established provenance; it does not enumerate
source roles as camera labels. -/
def canonicalC3SixSourceParameterValue (z w : ℂ) :
    CanonicalC3SixSourceParameterRole → ℂ
  | .z => z
  | .w => w
  | .reflectedZ => reflectedParameter z

/-- The factorization-camera ledger of the initial positive vertex is empty. -/
theorem cameraLogContributionVectorComplex_one_eq_zero :
    cameraLogContributionVectorComplex 1 = 0 := by
  ext p
  simp [cameraLogContributionVectorComplex_apply]

/-- Consequently, the current camera-resolved logarithmic value vanishes at
the initial positive vertex, for every complex parameter. -/
theorem cameraResolvedLogDirichletValue_zero_eq_zero (s : ℂ) :
    cameraResolvedLogDirichletValue s 0 = 0 := by
  rw [cameraResolvedLogDirichletValue]
  simp [cameraLogContributionVectorComplex_one_eq_zero]

/-- The ordinary Dirichlet source retains the incoming boundary seed at the
same vertex. -/
theorem positiveDirichletValue_zero_eq_one (s : ℂ) :
    positiveDirichletValue s 0 = 1 := by
  simp [positiveDirichletValue]

/-- Exact mismatch of the only existing camera-resolved value channel with
the ordinary boundary source.  This residual is the missing incoming/boundary
contribution; it is not a camera cross-term and cannot be removed by
relabeling the existing logarithmic channels. -/
def cameraResolvedOrdinaryBoundaryReuseResidual (s : ℂ) : ℂ :=
  positiveDirichletValue s 0 -
    cameraComplexSynthesis (cameraResolvedLogDirichletValue s 0)

theorem cameraResolvedOrdinaryBoundaryReuseResidual_eq_one (s : ℂ) :
    cameraResolvedOrdinaryBoundaryReuseResidual s = 1 := by
  rw [cameraResolvedOrdinaryBoundaryReuseResidual,
    cameraResolvedLogDirichletValue_zero_eq_zero,
    map_zero, positiveDirichletValue_zero_eq_one]
  norm_num

/-- The extant logarithmic camera synthesis is not an ordinary-source
synthesis, already at the incoming boundary atom. -/
theorem cameraComplexSynthesis_cameraResolvedLogDirichletValue_zero_ne_ordinary
    (s : ℂ) :
    cameraComplexSynthesis (cameraResolvedLogDirichletValue s 0) ≠
      positiveDirichletValue s 0 := by
  intro h
  have hres := cameraResolvedOrdinaryBoundaryReuseResidual_eq_one s
  rw [cameraResolvedOrdinaryBoundaryReuseResidual, h,
    sub_self] at hres
  norm_num at hres

/-- The role which blocks the presently available promotion is the ordinary
source role, uniformly at all three parameter provenances.  The log-jet role
is resolved by `cameraResolvedLogSlopeChannel`; the ordinary role requires a
new boundary-aware camera channel rather than reuse of that log resolver. -/
theorem canonicalC3SixSourceOrdinaryRole_not_resolved_by_existing_logCameraValue
    (_parameter : CanonicalC3SixSourceParameterRole) (s : ℂ) :
    cameraComplexSynthesis (cameraResolvedLogDirichletValue s 0) ≠
      positiveDirichletValue s 0 :=
  cameraComplexSynthesis_cameraResolvedLogDirichletValue_zero_ne_ordinary s

/-- The same unit residual occurs at each of the three ordinary six-source
parameter roles.  Thus reflected evaluation preserves the obstruction rather
than repairing it by a relabeling of log-camera channels. -/
theorem canonicalC3SixSourceOrdinaryRole_logCameraReuseResidual_eq_one
    (z w : ℂ) (parameter : CanonicalC3SixSourceParameterRole) :
    cameraResolvedOrdinaryBoundaryReuseResidual
      (canonicalC3SixSourceParameterValue z w parameter) = 1 :=
  cameraResolvedOrdinaryBoundaryReuseResidual_eq_one _

end

end CarrySelfAdjointOperator

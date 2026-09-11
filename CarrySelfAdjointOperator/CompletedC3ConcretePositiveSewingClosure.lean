import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CarrySelfAdjointOperator.CompletedC3ConcreteDressedLowOrderAudit
import CarrySelfAdjointOperator.CompletedC3GeometricCutoffCalibration
import Mathlib.Tactic

/-!
# Exact residual for the concrete C3 positive sewing gate

The concrete real-axis positive carrier is already channel-complete: its
ordinary, logarithmic, and retained precompression residual coordinates are
orthogonal.  The final all-cutoff C3 readout is independently known to be the
completed `dslope` kernel.  This module does not assert that those two scalar
objects coincide.  It names their difference, opens the positive side into
its three channels, and proves an exact central witness showing that the
standard metric cannot sew to the readout.

The result is a reduction, rather than a new carrier.  It leaves open the
possibility of a different positive metric or a transported state, while
certifying the failure of the fixed concrete state used by the existing HP
constructor.
-/

open scoped ComplexOrder InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The exact complex defect of the concrete channel-complete positive sewing
at a real pair.  Its right side is deliberately written through the named
positive kernel so that the carrier and its three orthogonal channels remain
visible in the API. -/
def canonicalCompletedC3ConcretePositiveSewingDefect
    (M : ℕ) (x z : ℝ) : ℂ :=
  canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z -
    canonicalCompletedC3RealAxisPositiveKernel (x : ℂ) (z : ℂ)

/-- Vanishing of the named defect is exactly the pointwise sewing equality at
one cutoff and one pair. -/
theorem canonicalCompletedC3ConcretePositiveSewingDefect_eq_zero_iff
    (M : ℕ) (x z : ℝ)
    (_hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (_hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    canonicalCompletedC3ConcretePositiveSewingDefect M x z = 0 ↔
      canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z =
        inner ℂ
          (canonicalCompletedC3RealAxisPositiveState (x : ℂ))
          (canonicalCompletedC3RealAxisPositiveState (z : ℂ)) := by
  unfold canonicalCompletedC3ConcretePositiveSewingDefect
    canonicalCompletedC3RealAxisPositiveKernel
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

/-- The global sewing predicate is equivalent to vanishing of the explicit
complex defect at every allowed real pair and every cutoff. -/
theorem canonicalCompletedC3ConcreteRealAxisPositiveSewing_iff_defect_zero :
    CanonicalCompletedC3ConcreteRealAxisPositiveSewing ↔
      ∀ (M : ℕ) (x z : ℝ),
        completedNativeOperatorCharacteristic (x : ℂ) ≠ 0 →
        completedNativeOperatorCharacteristic (z : ℂ) ≠ 0 →
        canonicalCompletedC3ConcretePositiveSewingDefect M x z = 0 := by
  constructor
  · intro h M x z hxF hzF
    exact
      (canonicalCompletedC3ConcretePositiveSewingDefect_eq_zero_iff
        M x z hxF hzF).mpr (h M x z hxF hzF)
  · intro h M x z hxF hzF
    exact
      (canonicalCompletedC3ConcretePositiveSewingDefect_eq_zero_iff
        M x z hxF hzF).mp (h M x z hxF hzF)

/-- On the nonvanishing real axis the defect is the completed `dslope` readout
minus the fixed positive-carrier Gram.  The cutoff disappears by an exact
identity, not by a limit. -/
theorem canonicalCompletedC3ConcretePositiveSewingDefect_eq_dslope_sub_positiveKernel
    (M : ℕ) (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    canonicalCompletedC3ConcretePositiveSewingDefect M x z =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ) -
        canonicalCompletedC3RealAxisPositiveKernel (x : ℂ) (z : ℂ) := by
  unfold canonicalCompletedC3ConcretePositiveSewingDefect
  rw [canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope
    M x z hxF hzF]

/-- The exact defect is cutoff-independent wherever the completed
characteristic does not vanish. -/
theorem canonicalCompletedC3ConcretePositiveSewingDefect_cutoff_independent
    (M N : ℕ) (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    canonicalCompletedC3ConcretePositiveSewingDefect M x z =
      canonicalCompletedC3ConcretePositiveSewingDefect N x z := by
  rw [canonicalCompletedC3ConcretePositiveSewingDefect_eq_dslope_sub_positiveKernel
      M x z hxF hzF,
    canonicalCompletedC3ConcretePositiveSewingDefect_eq_dslope_sub_positiveKernel
      N x z hxF hzF]

/-- The positive side of the defect is exactly the orthogonal sum of its
ordinary, log-jet, and retained real residual channel products.  No scalar
cross-term is silently discarded: this is the named source-channel identity
from the concrete positive carrier. -/
theorem canonicalCompletedC3ConcretePositiveSewingDefect_eq_readout_sub_sourceChannelSum
    (M : ℕ) (x z : ℝ) :
    canonicalCompletedC3ConcretePositiveSewingDefect M x z =
      canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z -
        (inner ℂ
            (canonicalCompletedC3RealAxisOrdinaryState (x : ℂ))
            (canonicalCompletedC3RealAxisOrdinaryState (z : ℂ)) +
          inner ℂ
            (canonicalCompletedC3RealAxisLogJetState (x : ℂ))
            (canonicalCompletedC3RealAxisLogJetState (z : ℂ)) +
          ((inner ℝ
            (canonicalCompletedC3RealAxisResidualState (x : ℂ))
            (canonicalCompletedC3RealAxisResidualState (z : ℂ)) : ℝ) : ℂ)) := by
  unfold canonicalCompletedC3ConcretePositiveSewingDefect
  rw [canonicalCompletedC3RealAxisPositiveKernel_eq_sourceChannelSum]

/-- Name the remaining channel-complete sewing residual.  It is a scalar
readout defect, not the retained residual state itself. -/
def canonicalCompletedC3ConcretePositiveSewingChannelResidual
    (M : ℕ) (x z : ℝ) : ℂ :=
  canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z -
    (inner ℂ
        (canonicalCompletedC3RealAxisOrdinaryState (x : ℂ))
        (canonicalCompletedC3RealAxisOrdinaryState (z : ℂ)) +
      inner ℂ
        (canonicalCompletedC3RealAxisLogJetState (x : ℂ))
        (canonicalCompletedC3RealAxisLogJetState (z : ℂ)) +
      ((inner ℝ
        (canonicalCompletedC3RealAxisResidualState (x : ℂ))
        (canonicalCompletedC3RealAxisResidualState (z : ℂ)) : ℝ) : ℂ))

/-- The channel residual is exactly the total concrete positive sewing
residual. -/
theorem canonicalCompletedC3ConcretePositiveSewingChannelResidual_eq_defect
    (M : ℕ) (x z : ℝ) :
    canonicalCompletedC3ConcretePositiveSewingChannelResidual M x z =
      canonicalCompletedC3ConcretePositiveSewingDefect M x z := by
  rw [canonicalCompletedC3ConcretePositiveSewingDefect_eq_readout_sub_sourceChannelSum]
  rfl

/-- After restricting to nonzero characteristic points, the channel residual
has an equally exact `dslope` description.  Thus the cutoff is absent from
the only unresolved equality. -/
theorem canonicalCompletedC3ConcretePositiveSewingChannelResidual_eq_dslope_sub_sourceChannelSum
    (M : ℕ) (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    canonicalCompletedC3ConcretePositiveSewingChannelResidual M x z =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ) -
        (inner ℂ
            (canonicalCompletedC3RealAxisOrdinaryState (x : ℂ))
            (canonicalCompletedC3RealAxisOrdinaryState (z : ℂ)) +
          inner ℂ
            (canonicalCompletedC3RealAxisLogJetState (x : ℂ))
            (canonicalCompletedC3RealAxisLogJetState (z : ℂ)) +
          ((inner ℝ
            (canonicalCompletedC3RealAxisResidualState (x : ℂ))
            (canonicalCompletedC3RealAxisResidualState (z : ℂ)) : ℝ) : ℂ)) := by
  unfold canonicalCompletedC3ConcretePositiveSewingChannelResidual
  rw [canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope
    M x z hxF hzF]

/-- The full sewing gate is equivalent to vanishing of the single residual
left after the ordinary, log-jet, and retained residual channels have been
opened. -/
theorem canonicalCompletedC3ConcreteRealAxisPositiveSewing_iff_channelResidual_zero :
    CanonicalCompletedC3ConcreteRealAxisPositiveSewing ↔
      ∀ (M : ℕ) (x z : ℝ),
        completedNativeOperatorCharacteristic (x : ℂ) ≠ 0 →
        completedNativeOperatorCharacteristic (z : ℂ) ≠ 0 →
        canonicalCompletedC3ConcretePositiveSewingChannelResidual M x z = 0 := by
  rw [canonicalCompletedC3ConcreteRealAxisPositiveSewing_iff_defect_zero]
  constructor
  · intro h M x z hxF hzF
    rw [canonicalCompletedC3ConcretePositiveSewingChannelResidual_eq_defect]
    exact h M x z hxF hzF
  · intro h M x z hxF hzF
    have hh := h M x z hxF hzF
    rw [canonicalCompletedC3ConcretePositiveSewingChannelResidual_eq_defect] at hh
    exact hh

/-- At the central real-axis pair, the complex defect has real part equal to
minus the already calibrated central moment defect.  The identity uses the
exact diagonal closure of the readout and no cutoff limit. -/
theorem canonicalCompletedC3ConcretePositiveSewingDefect_zero_zero_re_eq_neg_centralMomentDefect
    (M : ℕ) :
    (canonicalCompletedC3ConcretePositiveSewingDefect M 0 0).re =
      -canonicalCompletedC3ConcreteDressedCentralMomentDefect := by
  unfold canonicalCompletedC3ConcretePositiveSewingDefect
  rw [canonicalCompletedC3AllCutoffOrientedRealKernelReadout_zero_zero]
  unfold canonicalCompletedC3ConcreteDressedCentralMomentDefect
  simp only [Complex.sub_re, Complex.ofReal_re]
  norm_num

/-- At the central pair the channel residual has the same signed value as
the total defect. -/
theorem canonicalCompletedC3ConcretePositiveSewingChannelResidual_zero_zero_re_eq_neg_centralMomentDefect
    (M : ℕ) :
    (canonicalCompletedC3ConcretePositiveSewingChannelResidual M 0 0).re =
      -canonicalCompletedC3ConcreteDressedCentralMomentDefect := by
  rw [canonicalCompletedC3ConcretePositiveSewingChannelResidual_eq_defect,
    canonicalCompletedC3ConcretePositiveSewingDefect_zero_zero_re_eq_neg_centralMomentDefect]

/-- The central channel residual is strictly negative in real part. -/
theorem canonicalCompletedC3ConcretePositiveSewingChannelResidual_zero_zero_re_neg
    (M : ℕ) :
    (canonicalCompletedC3ConcretePositiveSewingChannelResidual M 0 0).re < 0 := by
  rw [canonicalCompletedC3ConcretePositiveSewingChannelResidual_eq_defect,
    canonicalCompletedC3ConcretePositiveSewingDefect_zero_zero_re_eq_neg_centralMomentDefect]
  exact neg_lt_zero.mpr canonicalCompletedC3ConcreteDressedCentralMomentDefect_pos

/-- The central defect is nonzero for every cutoff.  This is an explicit
witness against concrete positive sewing at `(M,0,0)`. -/
theorem canonicalCompletedC3ConcretePositiveSewingDefect_zero_zero_ne_zero
    (M : ℕ) :
    canonicalCompletedC3ConcretePositiveSewingDefect M 0 0 ≠ 0 := by
  intro hzero
  have hres :
      canonicalCompletedC3ConcretePositiveSewingChannelResidual M 0 0 = 0 := by
    rw [canonicalCompletedC3ConcretePositiveSewingChannelResidual_eq_defect]
    exact hzero
  have hre := congrArg Complex.re hres
  rw [Complex.zero_re] at hre
  exact (ne_of_lt
    (canonicalCompletedC3ConcretePositiveSewingChannelResidual_zero_zero_re_neg M))
    hre

/-- The fixed concrete sewing gate is uninhabited, now witnessed directly by
its named defect rather than only through the older calibration theorem. -/
theorem not_canonicalCompletedC3ConcreteRealAxisPositiveSewing_of_defect :
    ¬ CanonicalCompletedC3ConcreteRealAxisPositiveSewing := by
  intro hsewing
  have hzero := hsewing 0 0 0
    completedNativeOperatorCharacteristic_zero_ne_zero
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hdefect :=
    (canonicalCompletedC3ConcretePositiveSewingDefect_eq_zero_iff
      0 0 0 completedNativeOperatorCharacteristic_zero_ne_zero
        completedNativeOperatorCharacteristic_zero_ne_zero).mpr hzero
  exact canonicalCompletedC3ConcretePositiveSewingDefect_zero_zero_ne_zero 0 hdefect

/-- The fixed concrete positive state therefore cannot supply the real-axis
kernel input required by the downstream HP certificate. -/
theorem not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3_of_defect :
    ¬ HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState := by
  intro hkernel
  exact not_canonicalCompletedC3ConcreteRealAxisPositiveSewing_of_defect
    (canonicalCompletedC3ConcreteRealAxisPositiveSewing_iff_realAxisKernel.mpr
      hkernel)

end

end CarrySelfAdjointOperator

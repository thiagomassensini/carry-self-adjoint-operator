import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization
import CPFormal.Analytic.CpTfvdSeededNativeMomentSourceAudit

/-!
# Completed C3 TFVD--Bessel gate bridge

The historical seeded TFVD route and the completed C3 Green--Wronskian route
isolate the same remaining statement at a Genuine zero.  This file records the
equivalence without choosing a global moment source or assuming that the
structural channels vanish.

At every nonempty seeded cutoff, the following are equivalent:

* the completed C3 provenance/off-diagonal/residual triple tends to zero;
* the seeded TFVD Bessel energies are uniformly bounded over finite prime
  atlases;
* one fixed-time native tower state realizes every prime Green moment;
* the reflected Green profile family transports to a fixed-time moment state.

The existing source audit proves that constructing the common moment state is
already equivalent to the half-abscissa.  Thus these equivalences identify the
missing cross-package coefficient theorem; they do not manufacture it from the
finite TFVD return or from Parseval normalization.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

open scoped Topology

noncomputable section

/-- The explicit three-channel no-leak statement at one Genuine parameter. -/
def CanonicalC3StructuralNoLeakAt (s : ℂ) : Prop :=
  Tendsto
    (fun M : ℕ => canonicalC3FiniteMixedHeightStructuralDefect M s s)
    atTop (nhds 0)

/-- The current completed C3 no-leak gate is exactly the historical uniform
seeded TFVD Bessel budget, at any nonempty seeded cutoff. -/
theorem canonicalC3StructuralNoLeakAt_iff_seededTfvdBesselBudget
    (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    CanonicalC3StructuralNoLeakAt s ↔
      SeededTfvdFiniteBesselEnergiesBounded N s := by
  unfold CanonicalC3StructuralNoLeakAt
  rw [canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_at_genuineZero_iff
      hs hzero,
    seededTfvdFiniteBesselEnergiesBounded_iff_re_eq_half N hN hs]

/-- Equivalently, no-leak is the existence of one atlas-independent native
tower source whose fixed-time moments recover all prime Green readouts. -/
theorem canonicalC3StructuralNoLeakAt_iff_exists_nativeMomentSource
    (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    CanonicalC3StructuralNoLeakAt s ↔
      ∃ x : NativeGpreTowerHilbert,
        IsNativeGprePrimeMomentRealizationAt 1 (3 * N) s x := by
  unfold CanonicalC3StructuralNoLeakAt
  rw [canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_at_genuineZero_iff
      hs hzero,
    exists_seededTfvdNativeMomentSource_iff_re_eq_half N hN hs]

/-- The same gate in the reflected-profile language: the already constructed
universal Green energy requires a fixed native-time moment realization. -/
theorem canonicalC3StructuralNoLeakAt_iff_reflectedGapFixedTimeMomentState
    (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    CanonicalC3StructuralNoLeakAt s ↔
      NativeGpreReflectedGapHasFixedTimeMomentStateAt (3 * N) s := by
  unfold CanonicalC3StructuralNoLeakAt
  rw [canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_at_genuineZero_iff
      hs hzero,
    nativeGpreReflectedGapHasFixedTimeMomentStateAt_iff_critical
      (3 * N) (by omega) hs]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-- A concrete fixed-time native moment source discharges the completed C3
no-leak gate.  The source remains explicit in the hypotheses. -/
theorem canonicalC3StructuralNoLeakAt_of_nativeMomentSource
    (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (x : NativeGpreTowerHilbert)
    (hx : IsNativeGprePrimeMomentRealizationAt 1 (3 * N) s x) :
    CanonicalC3StructuralNoLeakAt s :=
  (canonicalC3StructuralNoLeakAt_iff_exists_nativeMomentSource
    N hN hs hzero).2 ⟨x, hx⟩

end

end CarrySelfAdjointOperator

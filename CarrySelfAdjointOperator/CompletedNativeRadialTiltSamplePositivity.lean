import CarrySelfAdjointOperator.CanonicalCompletedC3GammaDslopeGram
import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerBoundaryDefect
import CarrySelfAdjointOperator.CompletedNativeDslopeSamplePositivity
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceVectorLimit
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Radial tilt samples for the completed-native kernel

The concrete C3 gamma state is defined away from the real height axis.  The
usual centered forward-difference grid contains the origin, so it cannot be
fed directly to that state.  This file records the canonical off-axis grid

`(n + 1) * I / (k + 1)`

and proves that its gamma kernel is positive semidefinite at every finite
level.  It then isolates the exact division-free boundary identity which
identifies that positive Gram with the completed-native polarized `dslope` on
the same grid.  No zero-set, Stieltjes, Jacobi, or confinement hypothesis is
used.
-/

namespace CarrySelfAdjointOperator

open scoped ComplexConjugate ComplexOrder InnerProductSpace
open Filter Topology

noncomputable section

/-- Positive imaginary step on the canonical shrinking radial grid. -/
def canonicalCompletedC3RadialTiltStep (k : ℕ) : ℂ :=
  Complex.I * canonicalGreenJetStep k

/-- The shifted radial grid avoids the real axis while converging to the
center for every fixed sample index. -/
def canonicalCompletedC3RadialTiltPoint (k n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) * canonicalCompletedC3RadialTiltStep k

@[simp] theorem canonicalCompletedC3RadialTiltPoint_im
    (k n : ℕ) :
    (canonicalCompletedC3RadialTiltPoint k n).im =
      ((n : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ := by
  have hstep :
      canonicalGreenJetStep k =
        ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
    rw [← canonicalGreenJetRealStep_coe]
    rfl
  rw [canonicalCompletedC3RadialTiltPoint,
    canonicalCompletedC3RadialTiltStep, hstep]
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  push_cast
  ring

theorem canonicalCompletedC3RadialTiltPoint_im_pos
    (k n : ℕ) :
    0 < (canonicalCompletedC3RadialTiltPoint k n).im := by
  rw [canonicalCompletedC3RadialTiltPoint_im]
  positivity

theorem canonicalCompletedC3RadialTiltPoint_im_ne_zero
    (k n : ℕ) :
    (canonicalCompletedC3RadialTiltPoint k n).im ≠ 0 :=
  ne_of_gt (canonicalCompletedC3RadialTiltPoint_im_pos k n)

/-- Every fixed radial sample approaches the completed-native Taylor center. -/
theorem canonicalCompletedC3RadialTiltPoint_tendsto_zero (n : ℕ) :
    Tendsto (fun k : ℕ => canonicalCompletedC3RadialTiltPoint k n)
      atTop (nhds 0) := by
  unfold canonicalCompletedC3RadialTiltPoint
    canonicalCompletedC3RadialTiltStep
  simpa only [mul_assoc, mul_zero] using
    canonicalGreenJetStep_tendsto_zero.const_mul
      (((n + 1 : ℕ) : ℂ) * Complex.I)

/-- For every fixed stencil coordinate, sufficiently small radial tilt lies
inside the completed-native strip and avoids zeros of the characteristic. -/
theorem canonicalCompletedC3RadialTiltPoint_eventually_admissible (n : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      canonicalCompletedC3RadialTiltPoint k n ∈ completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k n) ≠ 0 := by
  have hpoint := canonicalCompletedC3RadialTiltPoint_tendsto_zero n
  have hdomain := hpoint.eventually
    (isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain)
  have hnonzero := hpoint.eventually
    (completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero)
  exact hdomain.and hnonzero

/-- The full, uncollapsed gamma Gram on the shifted radial grid. -/
def canonicalCompletedC3RadialGammaSampleMatrix (k N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3PolarizedGammaKernel
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)

/-- Every finite radial gamma sample is positive semidefinite because all
entries are products of vectors in the same global Naimark space. -/
theorem canonicalCompletedC3RadialGammaSampleMatrix_posSemidef
    (k N : ℕ) :
    (canonicalCompletedC3RadialGammaSampleMatrix k N).PosSemidef := by
  simpa [canonicalCompletedC3RadialGammaSampleMatrix] using
    (canonicalCompletedC3PolarizedGammaKernel_posSemidef
      (point := fun i : Fin N =>
        canonicalCompletedC3RadialTiltPoint k i)
      (fun i => canonicalCompletedC3RadialTiltPoint_im_ne_zero k i))

/-- The completed-native polarized divided-slope sampled on exactly the same
shifted radial grid as the gamma Gram. -/
def canonicalCompletedNativeRadialDslopeSampleMatrix (k N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)

theorem canonicalCompletedC3RadialTilt_separation_ne_zero
    (k i j : ℕ) :
    canonicalCompletedC3RadialTiltPoint k j -
        conj (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  change
    (canonicalCompletedC3RadialTiltPoint k j -
      conj (canonicalCompletedC3RadialTiltPoint k i)).im = 0 at him
  have hj := canonicalCompletedC3RadialTiltPoint_im_pos k j
  have hi := canonicalCompletedC3RadialTiltPoint_im_pos k i
  rw [Complex.sub_im, Complex.conj_im] at him
  linarith

/-- On one finite radial grid, the division-free boundary sewing identifies
the positive gamma Gram with the completed-native polarized `dslope` matrix.
The premise is exactly the numerator equality already exposed by
`canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_boundaryReadout`.
-/
theorem canonicalCompletedC3RadialGammaSampleMatrix_eq_dslope
    (k N : ℕ)
    (hboundary : ∀ i j : Fin N,
      canonicalCompletedC3PolarizedGammaBoundaryReadout
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) =
        (canonicalCompletedC3RadialTiltPoint k j -
            conj (canonicalCompletedC3RadialTiltPoint k i)) *
          canonicalCompletedNativePolarizedDslopeKernel
            (canonicalCompletedC3RadialTiltPoint k i)
            (canonicalCompletedC3RadialTiltPoint k j)) :
    canonicalCompletedC3RadialGammaSampleMatrix k N =
      canonicalCompletedNativeRadialDslopeSampleMatrix k N := by
  ext i j
  exact
    (canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_boundaryReadout
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
      (canonicalCompletedC3RadialTilt_separation_ne_zero k i j)).2
      (hboundary i j)

/-- Hence the radial completed-native `dslope` samples are positive whenever
the existing division-free C3 boundary readout closes on that finite grid. -/
theorem canonicalCompletedNativeRadialDslopeSampleMatrix_posSemidef
    (k N : ℕ)
    (hboundary : ∀ i j : Fin N,
      canonicalCompletedC3PolarizedGammaBoundaryReadout
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) =
        (canonicalCompletedC3RadialTiltPoint k j -
            conj (canonicalCompletedC3RadialTiltPoint k i)) *
          canonicalCompletedNativePolarizedDslopeKernel
            (canonicalCompletedC3RadialTiltPoint k i)
            (canonicalCompletedC3RadialTiltPoint k j)) :
    (canonicalCompletedNativeRadialDslopeSampleMatrix k N).PosSemidef := by
  rw [← canonicalCompletedC3RadialGammaSampleMatrix_eq_dslope k N hboundary]
  exact canonicalCompletedC3RadialGammaSampleMatrix_posSemidef k N

/-! ## Shifted forward differences

The gamma state is not defined at the centered origin.  The following finite
algebra moves every stencil one step away from the origin without changing its
limiting Taylor coefficient.
-/

theorem completedGreenForwardDifference_iter_apply_step
    {E : Type*} [AddCommGroup E]
    (h : ℂ) (f : ℂ → E) (p : ℕ) :
    (completedGreenForwardDifference h)^[p] f h =
      (completedGreenForwardDifference h)^[p] f 0 +
        (completedGreenForwardDifference h)^[p + 1] f 0 := by
  rw [Function.iterate_succ_apply']
  change (completedGreenForwardDifference h)^[p] f h =
    (completedGreenForwardDifference h)^[p] f 0 +
      ((completedGreenForwardDifference h)^[p] f (0 + h) -
        (completedGreenForwardDifference h)^[p] f 0)
  simp only [zero_add]
  abel

theorem completedGreenForwardDifference_iter_add
    {E : Type*} [AddCommGroup E]
    (h : ℂ) (f g : ℂ → E) (p : ℕ) :
    (completedGreenForwardDifference h)^[p] (f + g) =
      (completedGreenForwardDifference h)^[p] f +
        (completedGreenForwardDifference h)^[p] g := by
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih]
      funext z
      simp [completedGreenForwardDifference]
      abel

/-- Unnormalized mixed forward difference based at the centered origin. -/
def completedGreenKernelTwoStepRawDifference
    (kernel : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ) : ℂ :=
  (completedGreenForwardDifference h)^[p]
    (fun w => (completedGreenForwardDifference g)^[q] (kernel w) 0) 0

/-- The same mixed difference with each stencil based at its first nonzero
sample point. -/
def completedGreenKernelTwoStepShiftedRawDifference
    (kernel : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ) : ℂ :=
  (completedGreenForwardDifference h)^[p]
    (fun w => (completedGreenForwardDifference g)^[q] (kernel w) g) h

/-- Shifting both stencils by one step adds only the adjacent three higher
order differences.  This is an exact identity in every additive target. -/
theorem completedGreenKernelTwoStepShiftedRawDifference_eq
    (kernel : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ) :
    completedGreenKernelTwoStepShiftedRawDifference kernel h g p q =
      completedGreenKernelTwoStepRawDifference kernel h g p q +
      completedGreenKernelTwoStepRawDifference kernel h g p (q + 1) +
      completedGreenKernelTwoStepRawDifference kernel h g (p + 1) q +
      completedGreenKernelTwoStepRawDifference kernel h g (p + 1) (q + 1) := by
  let fq : ℂ → ℂ := fun w =>
    (completedGreenForwardDifference g)^[q] (kernel w) 0
  let fq1 : ℂ → ℂ := fun w =>
    (completedGreenForwardDifference g)^[q + 1] (kernel w) 0
  have hinner :
      (fun w => (completedGreenForwardDifference g)^[q] (kernel w) g) =
        fq + fq1 := by
    funext w
    exact completedGreenForwardDifference_iter_apply_step g (kernel w) q
  rw [completedGreenKernelTwoStepShiftedRawDifference, hinner,
    completedGreenForwardDifference_iter_add]
  simp only [Pi.add_apply]
  rw [
    completedGreenForwardDifference_iter_apply_step,
    completedGreenForwardDifference_iter_apply_step]
  simp only [fq, fq1, completedGreenKernelTwoStepRawDifference]
  ring

/-- Analytically normalized mixed difference.  Unlike a Hilbert Gram
normalization, both variables are normalized linearly; this is the natural
normalization after conjugating the first radial coordinate. -/
def completedGreenAnalyticTwoStepForwardDifference
    (kernel : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ) : ℂ :=
  (((p.factorial : ℂ) * h ^ p)⁻¹) *
    (((q.factorial : ℂ) * g ^ q)⁻¹) *
      completedGreenKernelTwoStepRawDifference kernel h g p q

/-- Shifted version of the analytic two-step normalization. -/
def completedGreenAnalyticTwoStepShiftedForwardDifference
    (kernel : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ) : ℂ :=
  (((p.factorial : ℂ) * h ^ p)⁻¹) *
    (((q.factorial : ℂ) * g ^ q)⁻¹) *
      completedGreenKernelTwoStepShiftedRawDifference kernel h g p q

/-- Exact normalized form of the one-step stencil shift. -/
theorem completedGreenAnalyticTwoStepShiftedForwardDifference_eq
    (kernel : ℂ → ℂ → ℂ) {h g : ℂ} (hh : h ≠ 0) (hg : g ≠ 0)
    (p q : ℕ) :
    completedGreenAnalyticTwoStepShiftedForwardDifference kernel h g p q =
      completedGreenAnalyticTwoStepForwardDifference kernel h g p q +
      ((q + 1 : ℕ) : ℂ) * g *
        completedGreenAnalyticTwoStepForwardDifference kernel h g p (q + 1) +
      ((p + 1 : ℕ) : ℂ) * h *
        completedGreenAnalyticTwoStepForwardDifference kernel h g (p + 1) q +
      (((p + 1 : ℕ) : ℂ) * h) * (((q + 1 : ℕ) : ℂ) * g) *
        completedGreenAnalyticTwoStepForwardDifference
          kernel h g (p + 1) (q + 1) := by
  rw [completedGreenAnalyticTwoStepShiftedForwardDifference,
    completedGreenKernelTwoStepShiftedRawDifference_eq]
  unfold completedGreenAnalyticTwoStepForwardDifference
  have hp : (p.factorial : ℂ) ≠ 0 := by
    exact_mod_cast p.factorial_ne_zero
  have hq : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast q.factorial_ne_zero
  have hp1 : (((p + 1).factorial : ℕ) : ℂ) =
      ((p + 1 : ℕ) : ℂ) * (p.factorial : ℂ) := by
    norm_cast
  have hq1 : (((q + 1).factorial : ℕ) : ℂ) =
      ((q + 1 : ℕ) : ℂ) * (q.factorial : ℂ) := by
    norm_cast
  rw [hp1, hq1]
  field_simp [hh, hg, hp, hq]
  ring

/-! ## Radial coefficient extraction -/

/-- First analytic endpoint step after conjugating a positive imaginary
height parameter. -/
def canonicalCompletedC3RadialFirstStep (k : ℕ) : ℂ :=
  -Complex.I * canonicalGreenJetStep k

/-- Second analytic endpoint step on the positive imaginary ray. -/
def canonicalCompletedC3RadialSecondStep (k : ℕ) : ℂ :=
  Complex.I * canonicalGreenJetStep k

theorem canonicalGreenJetStep_ne_zero (k : ℕ) :
    canonicalGreenJetStep k ≠ 0 := by
  unfold canonicalGreenJetStep
  exact inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero k)

theorem canonicalCompletedC3RadialFirstStep_ne_zero (k : ℕ) :
    canonicalCompletedC3RadialFirstStep k ≠ 0 := by
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (canonicalGreenJetStep_ne_zero k)

theorem canonicalCompletedC3RadialSecondStep_ne_zero (k : ℕ) :
    canonicalCompletedC3RadialSecondStep k ≠ 0 := by
  exact mul_ne_zero Complex.I_ne_zero (canonicalGreenJetStep_ne_zero k)

theorem canonicalCompletedC3RadialFirstStep_tendsto_zero :
    Tendsto canonicalCompletedC3RadialFirstStep atTop (nhds 0) := by
  change Tendsto (fun k => -Complex.I * canonicalGreenJetStep k)
    atTop (nhds 0)
  simpa only [mul_zero] using
    canonicalGreenJetStep_tendsto_zero.const_mul (-Complex.I)

theorem canonicalCompletedC3RadialSecondStep_tendsto_zero :
    Tendsto canonicalCompletedC3RadialSecondStep atTop (nhds 0) := by
  change Tendsto (fun k => Complex.I * canonicalGreenJetStep k)
    atTop (nhds 0)
  simpa only [mul_zero] using
    canonicalGreenJetStep_tendsto_zero.const_mul Complex.I

/-- Joint convergence of a scalar kernel passes through finite sampling on
the two conjugate radial rays. -/
theorem completedGreenTwoStepWeightedSum_radial_tendsto
    {kernel : ℂ → ℂ → ℂ} {coefficient : ℂ}
    (hkernel : Tendsto
      (fun points : ℂ × ℂ => kernel points.1 points.2)
      (nhds (0, 0)) (nhds coefficient))
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ =>
        completedGreenTwoStepWeightedSum kernel p q
          (canonicalCompletedC3RadialFirstStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2))
      atTop
      (nhds
        (∑ i ∈ Finset.range (p + 1),
          (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
            ∑ j ∈ Finset.range (q + 1),
              (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
                coefficient)) := by
  let rotatedKernel : ℂ → ℂ → ℂ := fun w z =>
    kernel (-Complex.I * w) (Complex.I * z)
  have hrotation : Tendsto
      (fun points : ℂ × ℂ =>
        (-Complex.I * points.1, Complex.I * points.2))
      (nhds (0, 0)) (nhds (0, 0)) := by
    have hcontinuous : ContinuousAt
      (fun points : ℂ × ℂ =>
        (-Complex.I * points.1, Complex.I * points.2)) (0, 0) := by
      fun_prop
    change Tendsto
      (fun points : ℂ × ℂ =>
        (-Complex.I * points.1, Complex.I * points.2))
      (nhds (0, 0))
      (nhds (-Complex.I * ((0, 0) : ℂ × ℂ).1,
        Complex.I * ((0, 0) : ℂ × ℂ).2)) at hcontinuous
    simpa using hcontinuous
  have hrotated : Tendsto
      (fun points : ℂ × ℂ => rotatedKernel points.1 points.2)
      (nhds (0, 0)) (nhds coefficient) :=
    hkernel.comp hrotation
  have hlimit := completedGreenTwoStepWeightedSum_tendsto
    hrotated p q
  simpa [rotatedKernel, canonicalCompletedC3RadialFirstStep,
    canonicalCompletedC3RadialSecondStep,
    completedGreenTwoStepWeightedSum, mul_assoc, mul_left_comm, mul_comm]
    using hlimit

/-- Every finite grid on a fixed rotation of the canonical shrinking step is
eventually contained in the analytic neighborhood of the centered iterates. -/
theorem completedGreenCenteredDslopeIter_rotatedGrid_eventually_differentiableAt
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (rotation : ℂ) (order : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (order + 1),
        ∀ n ∈ Finset.range order,
          DifferentiableAt ℂ
            (completedGreenCenteredDslopeIter response (n + 1))
            ((i : ℂ) * (rotation * canonicalGreenJetStep k)) := by
  rw [eventually_all_finset]
  intro i hi
  rw [eventually_all_finset]
  intro n hn
  have hanalytic :=
    (completedGreenCenteredDslopeIter_analyticAt
      hresponse (n + 1)).eventually_analyticAt
  have hpoint : Tendsto
      (fun k : ℕ => (i : ℂ) * (rotation * canonicalGreenJetStep k))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (canonicalGreenJetStep_tendsto_zero.const_mul rotation).const_mul (i : ℂ)
  exact (hpoint.eventually hanalytic).mono fun k hk => hk.differentiableAt

/-- The bivariate remainder has the same coefficient limit on the two
conjugate radial rays as on the real ray. -/
theorem completedGreenDslopeTwoStepRemainder_radial_tendsto
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ =>
        completedGreenDslopeTwoStepRemainder response p q
          (canonicalCompletedC3RadialFirstStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2))
      atTop
      (nhds ((p.factorial : ℂ) * (q.factorial : ℂ) *
        (iteratedDeriv (p + q + 1) response 0 /
          ((p + q + 1).factorial : ℂ)))) := by
  let shifted := completedGreenCenteredDslopeIter response (p + q)
  let coefficient := iteratedDeriv (p + q + 1) response 0 /
    ((p + q + 1).factorial : ℂ)
  have hshifted : AnalyticAt ℂ shifted 0 :=
    completedGreenCenteredDslopeIter_analyticAt hresponse (p + q)
  have hkernel : Tendsto
      (fun points : ℂ × ℂ => dslope shifted points.1 points.2)
      (nhds (0, 0)) (nhds coefficient) := by
    have hjoint := completedGreenDslope_tendsto_prod_of_analyticAt hshifted
    have hcoeff : deriv shifted 0 = coefficient :=
      deriv_completedGreenCenteredDslopeIter_zero hresponse (p + q)
    rw [hcoeff] at hjoint
    exact hjoint
  have hsum := completedGreenTwoStepWeightedSum_radial_tendsto
    hkernel p q
  have htarget :
      (∑ i ∈ Finset.range (p + 1),
        (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
          ∑ j ∈ Finset.range (q + 1),
            (completedGreenForwardWeight q j * (j : ℂ) ^ q) * coefficient) =
        (p.factorial : ℂ) * (q.factorial : ℂ) * coefficient := by
    rw [show (∑ j ∈ Finset.range (q + 1),
          (completedGreenForwardWeight q j * (j : ℂ) ^ q) * coefficient) =
        completedGreenForwardWeightPower q q * coefficient by
      unfold completedGreenForwardWeightPower
      rw [Finset.sum_mul]]
    rw [completedGreenForwardWeightPower_self]
    rw [show (∑ i ∈ Finset.range (p + 1),
          (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
            ((q.factorial : ℂ) * coefficient)) =
        completedGreenForwardWeightPower p p *
          ((q.factorial : ℂ) * coefficient) by
      unfold completedGreenForwardWeightPower
      rw [Finset.sum_mul]]
    rw [completedGreenForwardWeightPower_self]
    ring
  rw [htarget] at hsum
  simpa [completedGreenDslopeTwoStepRemainder, shifted, coefficient] using hsum

/-- The exact bivariate factorization is eventually valid on the two
conjugate radial grids. -/
theorem completedGreenDslopeTwoStepSum_radial_eventuallyEq_factor
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    (fun steps : ℕ × ℕ =>
      completedGreenDslopeTwoStepSum response p q
        (canonicalCompletedC3RadialFirstStep steps.1)
        (canonicalCompletedC3RadialSecondStep steps.2)) =ᶠ[atTop]
    (fun steps : ℕ × ℕ =>
      canonicalCompletedC3RadialFirstStep steps.1 ^ p *
        canonicalCompletedC3RadialSecondStep steps.2 ^ q *
          completedGreenDslopeTwoStepRemainder response p q
            (canonicalCompletedC3RadialFirstStep steps.1)
            (canonicalCompletedC3RadialSecondStep steps.2)) := by
  have hfirst :=
    completedGreenCenteredDslopeIter_rotatedGrid_eventually_differentiableAt
      hresponse (-Complex.I) p
  have hpAnalytic :=
    completedGreenCenteredDslopeIter_analyticAt hresponse p
  have hsecond :=
    completedGreenCenteredDslopeIter_rotatedGrid_eventually_differentiableAt
      hpAnalytic Complex.I q
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  filter_upwards [hfst.eventually hfirst, hsnd.eventually hsecond] with
      steps hfirstSteps hsecondSteps
  exact completedGreenDslopeTwoStepSum_factor_remainder response p q
    (canonicalCompletedC3RadialFirstStep steps.1)
    (canonicalCompletedC3RadialSecondStep steps.2)
    (fun i hi n hn => hfirstSteps i hi n (Finset.mem_range.mpr hn))
    (fun j hj n hn => hsecondSteps j hj n (Finset.mem_range.mpr hn))

/-- After analytic normalization, radial finite differences are eventually a
fixed factorial scale times the finite remainder. -/
theorem completedGreenAnalyticTwoStepForwardDifference_radial_eventuallyEq
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    (fun steps : ℕ × ℕ =>
      completedGreenAnalyticTwoStepForwardDifference
        (fun w z => dslope response w z)
        (canonicalCompletedC3RadialFirstStep steps.1)
        (canonicalCompletedC3RadialSecondStep steps.2) p q) =ᶠ[atTop]
    (fun steps : ℕ × ℕ =>
      (((p.factorial : ℂ) * (q.factorial : ℂ))⁻¹) *
        completedGreenDslopeTwoStepRemainder response p q
          (canonicalCompletedC3RadialFirstStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2)) := by
  have hfactor :=
    completedGreenDslopeTwoStepSum_radial_eventuallyEq_factor
      hresponse p q
  filter_upwards [hfactor] with steps hfactorSteps
  have hp : (p.factorial : ℂ) ≠ 0 := by
    exact_mod_cast p.factorial_ne_zero
  have hq : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast q.factorial_ne_zero
  have hh := canonicalCompletedC3RadialFirstStep_ne_zero steps.1
  have hg := canonicalCompletedC3RadialSecondStep_ne_zero steps.2
  rw [completedGreenAnalyticTwoStepForwardDifference,
    completedGreenKernelTwoStepRawDifference,
    completedGreenDslope_twoStepMixedForwardDifference_eq_sum,
    hfactorSteps]
  field_simp [hp, hq, hh, hg]

/-- Analytically normalized finite differences on the two conjugate radial
rays recover the same bivariate Taylor coefficient as the centered real
grid. -/
theorem completedGreenAnalyticTwoStepForwardDifference_radial_tendsto
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ =>
        completedGreenAnalyticTwoStepForwardDifference
          (fun w z => dslope response w z)
          (canonicalCompletedC3RadialFirstStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q)
      atTop
      (nhds (iteratedDeriv (p + q + 1) response 0 /
        ((p + q + 1).factorial : ℂ))) := by
  let scale : ℂ :=
    (((p.factorial : ℂ) * (q.factorial : ℂ))⁻¹)
  have hremainder :=
    completedGreenDslopeTwoStepRemainder_radial_tendsto hresponse p q
  have hscaled := hremainder.const_mul scale
  have hp : (p.factorial : ℂ) ≠ 0 := by
    exact_mod_cast p.factorial_ne_zero
  have hq : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast q.factorial_ne_zero
  have htarget : scale *
        ((p.factorial : ℂ) * (q.factorial : ℂ) *
          (iteratedDeriv (p + q + 1) response 0 /
            ((p + q + 1).factorial : ℂ))) =
      iteratedDeriv (p + q + 1) response 0 /
        ((p + q + 1).factorial : ℂ) := by
    dsimp [scale]
    field_simp [hp, hq]
  rw [htarget] at hscaled
  apply hscaled.congr'
  exact
    (completedGreenAnalyticTwoStepForwardDifference_radial_eventuallyEq
      hresponse p q).symm

/-- The one-step off-axis shift does not change the radial coefficient limit.
All correction terms carry at least one explicit shrinking step. -/
theorem completedGreenAnalyticTwoStepShiftedForwardDifference_radial_tendsto
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ =>
        completedGreenAnalyticTwoStepShiftedForwardDifference
          (fun w z => dslope response w z)
          (canonicalCompletedC3RadialFirstStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q)
      atTop
      (nhds (iteratedDeriv (p + q + 1) response 0 /
        ((p + q + 1).factorial : ℂ))) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hh : Tendsto
      (fun steps : ℕ × ℕ =>
        canonicalCompletedC3RadialFirstStep steps.1)
      atTop (nhds 0) :=
    canonicalCompletedC3RadialFirstStep_tendsto_zero.comp hfst
  have hg : Tendsto
      (fun steps : ℕ × ℕ =>
        canonicalCompletedC3RadialSecondStep steps.2)
      atTop (nhds 0) :=
    canonicalCompletedC3RadialSecondStep_tendsto_zero.comp hsnd
  have hmain :=
    completedGreenAnalyticTwoStepForwardDifference_radial_tendsto
      hresponse p q
  have hpq1 :=
    completedGreenAnalyticTwoStepForwardDifference_radial_tendsto
      hresponse p (q + 1)
  have hp1q :=
    completedGreenAnalyticTwoStepForwardDifference_radial_tendsto
      hresponse (p + 1) q
  have hp1q1 :=
    completedGreenAnalyticTwoStepForwardDifference_radial_tendsto
      hresponse (p + 1) (q + 1)
  have hqCorrection : Tendsto
      (fun steps : ℕ × ℕ =>
        (((q + 1 : ℕ) : ℂ) *
          canonicalCompletedC3RadialSecondStep steps.2) *
          completedGreenAnalyticTwoStepForwardDifference
            (fun w z => dslope response w z)
            (canonicalCompletedC3RadialFirstStep steps.1)
            (canonicalCompletedC3RadialSecondStep steps.2) p (q + 1))
      atTop (nhds 0) := by
    simpa only [zero_mul, mul_zero] using
      (hg.const_mul (((q + 1 : ℕ) : ℂ))).mul hpq1
  have hpCorrection : Tendsto
      (fun steps : ℕ × ℕ =>
        (((p + 1 : ℕ) : ℂ) *
          canonicalCompletedC3RadialFirstStep steps.1) *
          completedGreenAnalyticTwoStepForwardDifference
            (fun w z => dslope response w z)
            (canonicalCompletedC3RadialFirstStep steps.1)
            (canonicalCompletedC3RadialSecondStep steps.2) (p + 1) q)
      atTop (nhds 0) := by
    simpa only [zero_mul, mul_zero] using
      (hh.const_mul (((p + 1 : ℕ) : ℂ))).mul hp1q
  have hpqCorrection : Tendsto
      (fun steps : ℕ × ℕ =>
        ((((p + 1 : ℕ) : ℂ) *
            canonicalCompletedC3RadialFirstStep steps.1) *
          (((q + 1 : ℕ) : ℂ) *
            canonicalCompletedC3RadialSecondStep steps.2)) *
          completedGreenAnalyticTwoStepForwardDifference
            (fun w z => dslope response w z)
            (canonicalCompletedC3RadialFirstStep steps.1)
            (canonicalCompletedC3RadialSecondStep steps.2)
            (p + 1) (q + 1))
      atTop (nhds 0) := by
    have hscale : Tendsto
        (fun steps : ℕ × ℕ =>
          (((p + 1 : ℕ) : ℂ) *
              canonicalCompletedC3RadialFirstStep steps.1) *
            (((q + 1 : ℕ) : ℂ) *
              canonicalCompletedC3RadialSecondStep steps.2))
        atTop (nhds 0) := by
      simpa only [zero_mul, mul_zero] using
        (hh.const_mul (((p + 1 : ℕ) : ℂ))).mul
          (hg.const_mul (((q + 1 : ℕ) : ℂ)))
    simpa only [zero_mul, mul_zero] using hscale.mul hp1q1
  have hsum := ((hmain.add hqCorrection).add hpCorrection).add hpqCorrection
  have hsum' : Tendsto
      (fun x : ℕ × ℕ =>
        completedGreenAnalyticTwoStepForwardDifference
              (fun w z => dslope response w z)
              (canonicalCompletedC3RadialFirstStep x.1)
              (canonicalCompletedC3RadialSecondStep x.2) p q +
            (((q + 1 : ℕ) : ℂ) *
                canonicalCompletedC3RadialSecondStep x.2) *
              completedGreenAnalyticTwoStepForwardDifference
                (fun w z => dslope response w z)
                (canonicalCompletedC3RadialFirstStep x.1)
                (canonicalCompletedC3RadialSecondStep x.2) p (q + 1) +
          (((p + 1 : ℕ) : ℂ) *
              canonicalCompletedC3RadialFirstStep x.1) *
            completedGreenAnalyticTwoStepForwardDifference
              (fun w z => dslope response w z)
              (canonicalCompletedC3RadialFirstStep x.1)
              (canonicalCompletedC3RadialSecondStep x.2) (p + 1) q +
        ((((p + 1 : ℕ) : ℂ) *
              canonicalCompletedC3RadialFirstStep x.1) *
            (((q + 1 : ℕ) : ℂ) *
              canonicalCompletedC3RadialSecondStep x.2)) *
          completedGreenAnalyticTwoStepForwardDifference
            (fun w z => dslope response w z)
            (canonicalCompletedC3RadialFirstStep x.1)
            (canonicalCompletedC3RadialSecondStep x.2)
            (p + 1) (q + 1))
      atTop
      (nhds (iteratedDeriv (p + q + 1) response 0 /
        ((p + q + 1).factorial : ℂ))) := by
    simpa only [add_zero] using hsum
  apply hsum'.congr'
  filter_upwards with steps
  symm
  exact completedGreenAnalyticTwoStepShiftedForwardDifference_eq
    (fun w z => dslope response w z)
    (canonicalCompletedC3RadialFirstStep_ne_zero steps.1)
    (canonicalCompletedC3RadialSecondStep_ne_zero steps.2) p q

/-! ## Hilbert normalization of the polarized radial kernel -/

/-- Conjugating the input of a state function conjugates the step of every
iterated forward difference. -/
theorem completedGreenForwardDifference_iter_comp_conj
    {E : Type*} [AddCommGroup E]
    (h : ℂ) (f : ℂ → E) (p : ℕ) (z : ℂ) :
    (completedGreenForwardDifference h)^[p] (fun w => f (conj w)) z =
      (completedGreenForwardDifference (conj h))^[p] f (conj z) := by
  induction p generalizing z with
  | zero => rfl
  | succ p ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (completedGreenForwardDifference h)^[p]
          (fun w => f (conj w)) (z + h) -
        (completedGreenForwardDifference h)^[p]
          (fun w => f (conj w)) z = _
      rw [ih (z := z + h), ih (z := z)]
      simp only [map_add]
      rfl

/-- Hilbert-normalized shifted kernel difference.  The first scalar factor is
conjugated exactly as it is in an inner product. -/
def completedGreenKernelTwoStepShiftedForwardDifference
    (kernel : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ) : ℂ :=
  (starRingEnd ℂ) (((p.factorial : ℂ) * h ^ p)⁻¹) *
    (((q.factorial : ℂ) * g ^ q)⁻¹) *
      completedGreenKernelTwoStepShiftedRawDifference kernel h g p q

/-- For a Hermitian polarization `K(z,w)=L(conj z,w)`, Hilbert
normalization on `(h,g)` is literally analytic normalization on
`(conj h,g)`. -/
theorem completedGreenKernelTwoStepShiftedForwardDifference_polarized
    (kernel : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ) :
    completedGreenKernelTwoStepShiftedForwardDifference
        (fun z w => kernel (conj z) w) h g p q =
      completedGreenAnalyticTwoStepShiftedForwardDifference
        kernel (conj h) g p q := by
  have hraw :
      completedGreenKernelTwoStepShiftedRawDifference
          (fun z w => kernel (conj z) w) h g p q =
        completedGreenKernelTwoStepShiftedRawDifference
          kernel (conj h) g p q := by
    let fq : ℂ → ℂ := fun z =>
      (completedGreenForwardDifference g)^[q] (kernel z) g
    change (completedGreenForwardDifference h)^[p]
        (fun z => fq (conj z)) h =
      (completedGreenForwardDifference (conj h))^[p] fq (conj h)
    exact completedGreenForwardDifference_iter_comp_conj h fq p h
  rw [completedGreenKernelTwoStepShiftedForwardDifference,
    completedGreenAnalyticTwoStepShiftedForwardDifference, hraw]
  simp only [map_inv₀, map_mul, map_pow, map_natCast]

@[simp] theorem conj_canonicalCompletedC3RadialSecondStep
    (k : ℕ) :
    conj (canonicalCompletedC3RadialSecondStep k) =
      canonicalCompletedC3RadialFirstStep k := by
  simp [canonicalCompletedC3RadialFirstStep,
    canonicalCompletedC3RadialSecondStep, canonicalGreenJetStep]

/-- The completed-native polarized `dslope`, sampled on the shifted positive
imaginary ray and normalized as a Hilbert Gram, converges to the canonical
mixed Taylor coefficient. -/
theorem completedNativePolarizedDslope_shiftedRadial_tendsto
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ =>
        completedGreenKernelTwoStepShiftedForwardDifference
          canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q)
      atTop
      (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q)) := by
  have hlimit :=
    completedGreenAnalyticTwoStepShiftedForwardDifference_radial_tendsto
      completedNativeGreenNormalizedResponse_analyticAt p q
  have hcoefficient :
      iteratedDeriv (p + q + 1)
          (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion) 0 /
        ((p + q + 1).factorial : ℂ) =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q :=
    completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized p q
  rw [hcoefficient] at hlimit
  apply hlimit.congr'
  filter_upwards with steps
  symm
  change completedGreenKernelTwoStepShiftedForwardDifference
      (fun z w => dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (conj z) w)
      (canonicalCompletedC3RadialSecondStep steps.1)
      (canonicalCompletedC3RadialSecondStep steps.2) p q = _
  rw [completedGreenKernelTwoStepShiftedForwardDifference_polarized,
    conj_canonicalCompletedC3RadialSecondStep]

/-! ## Shifted radial Gamma jets -/

/-- Normalized state forward difference based at the first nonzero sample. -/
def completedGreenShiftedForwardDifferenceJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (state : ℂ → E) (h : ℂ) (order : ℕ) : E :=
  (((order.factorial : ℂ) * h ^ order)⁻¹) •
    (completedGreenForwardDifference h)^[order] state h

/-- Mixed shifted differences of an inner-product kernel are exactly the
inner products of the corresponding shifted state jets. -/
theorem inner_completedGreenShiftedForwardDifferenceJet_eq_kernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E) (h g : ℂ) (p q : ℕ) :
    inner ℂ
        (completedGreenShiftedForwardDifferenceJet state h p)
        (completedGreenShiftedForwardDifferenceJet state g q) =
      completedGreenKernelTwoStepShiftedForwardDifference
        (fun w z => inner ℂ (state w) (state z)) h g p q := by
  have hright :
      (fun w => (completedGreenForwardDifference g)^[q]
        (fun z => inner ℂ (state w) (state z)) g) =
      (fun w => inner ℂ (state w)
        ((completedGreenForwardDifference g)^[q] state g)) := by
    funext w
    exact congrFun
      (completedGreenForwardDifference_iter_inner_right g state (state w) q) g
  have hmixed :
      completedGreenKernelTwoStepShiftedRawDifference
          (fun w z => inner ℂ (state w) (state z)) h g p q =
        inner ℂ
          ((completedGreenForwardDifference h)^[p] state h)
          ((completedGreenForwardDifference g)^[q] state g) := by
    rw [completedGreenKernelTwoStepShiftedRawDifference, hright]
    exact congrFun
      (completedGreenForwardDifference_iter_inner_left h state
        ((completedGreenForwardDifference g)^[q] state g) p) h
  unfold completedGreenShiftedForwardDifferenceJet
    completedGreenKernelTwoStepShiftedForwardDifference
  rw [inner_smul_left, inner_smul_right, ← hmixed]
  ring

/-- Equality of two kernels on the finite shifted sampling rectangle identifies
their normalized shifted mixed differences. -/
theorem completedGreenKernelTwoStepShiftedForwardDifference_eq_of_eq_on_grid
    (kernel kernel' : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ)
    (hkernel : ∀ i ∈ Finset.range (p + 1),
      ∀ j ∈ Finset.range (q + 1),
        kernel (h + i • h) (g + j • g) =
          kernel' (h + i • h) (g + j • g)) :
    completedGreenKernelTwoStepShiftedForwardDifference kernel h g p q =
      completedGreenKernelTwoStepShiftedForwardDifference kernel' h g p q := by
  unfold completedGreenKernelTwoStepShiftedForwardDifference
    completedGreenKernelTwoStepShiftedRawDifference
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  conv_rhs =>
    rw [completedGreenForwardDifference_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  conv_rhs =>
    rw [completedGreenForwardDifference_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact hkernel i hi j hj

/-- Globally totalized completed C3 gamma state.  Its value at the origin is
irrelevant to the shifted stencils, but totalization gives one honest function
on all of `ℂ`. -/
def canonicalCompletedC3TotalGammaState (z : ℂ) : CarryGammaComplexNaimark :=
  totalCarryGammaState canonicalCompletedC3SixCameraSource z

theorem canonicalCompletedC3TotalGammaState_of_im_ne_zero
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3TotalGammaState z =
      canonicalCompletedC3PolarizedGammaState z hz := by
  unfold canonicalCompletedC3TotalGammaState
    canonicalCompletedC3PolarizedGammaState carryGammaComplexState
  exact totalCarryGammaState_of_im_ne_zero
    canonicalCompletedC3SixCameraSource hz

theorem canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul
    (k n : ℕ) :
    canonicalCompletedC3RadialTiltPoint k n =
      canonicalCompletedC3RadialSecondStep k +
        n • canonicalCompletedC3RadialSecondStep k := by
  simp [canonicalCompletedC3RadialTiltPoint,
    canonicalCompletedC3RadialTiltStep,
    canonicalCompletedC3RadialSecondStep, nsmul_eq_mul]
  ring

theorem canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
    (k l i j : ℕ) :
    canonicalCompletedC3RadialTiltPoint l j -
        conj (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  change
    (canonicalCompletedC3RadialTiltPoint l j -
      conj (canonicalCompletedC3RadialTiltPoint k i)).im = 0 at him
  have hj := canonicalCompletedC3RadialTiltPoint_im_pos l j
  have hi := canonicalCompletedC3RadialTiltPoint_im_pos k i
  rw [Complex.sub_im, Complex.conj_im] at him
  linarith

/-- Exact radial restriction of the already identified division-free C3
boundary seam.  It contains no positivity assertion: it only says that the
boundary numerator and the completed-native numerator are the same on the
canonical off-axis grids. -/
def CanonicalCompletedC3RadialTiltBoundaryIntertwining : Prop :=
  ∀ k l i j : ℕ,
    canonicalCompletedC3PolarizedGammaBoundaryReadout
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint l j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero l j) =
      (canonicalCompletedC3RadialTiltPoint l j -
          conj (canonicalCompletedC3RadialTiltPoint k i)) *
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint l j)

/-- Local form of the radial boundary intertwining.  For each fixed finite
stencil, the numerator identity is only required eventually as both radial
steps tend to zero.  This is the exact strength used by coefficient
extraction; no global off-axis sewing is required. -/
def CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining : Prop :=
  ∀ p q : ℕ, ∀ᶠ steps : ℕ × ℕ in atTop,
    ∀ i ∈ Finset.range (p + 1), ∀ j ∈ Finset.range (q + 1),
      canonicalCompletedC3PolarizedGammaBoundaryReadout
          (canonicalCompletedC3RadialTiltPoint steps.1 i)
          (canonicalCompletedC3RadialTiltPoint steps.2 j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) =
        (canonicalCompletedC3RadialTiltPoint steps.2 j -
            conj (canonicalCompletedC3RadialTiltPoint steps.1 i)) *
          canonicalCompletedNativePolarizedDslopeKernel
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j)

/-- The same local gate expressed by the explicit completed C3
Gamma/ledger defect.  All radial, provenance, off-diagonal, residual, tail,
xi-weight, and archimedean channels remain inside this concrete defect. -/
def CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak : Prop :=
  ∀ p q : ℕ, ∀ᶠ steps : ℕ × ℕ in atTop,
    ∀ i ∈ Finset.range (p + 1), ∀ j ∈ Finset.range (q + 1),
      canonicalCompletedC3GammaLedgerBoundaryDefect 0
        (canonicalCompletedC3RadialTiltPoint steps.1 i)
        (canonicalCompletedC3RadialTiltPoint steps.2 j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) = 0

/-- Kernel-level form of the local radial gate.  It is deliberately stated
only on each fixed shrinking stencil, so no global off-axis identity is
hidden in the interface. -/
def CanonicalCompletedC3AsymptoticRadialGammaKernelIntertwining : Prop :=
  ∀ p q : ℕ, ∀ᶠ steps : ℕ × ℕ in atTop,
    ∀ i ∈ Finset.range (p + 1), ∀ j ∈ Finset.range (q + 1),
      canonicalCompletedC3PolarizedGammaKernel
          (canonicalCompletedC3RadialTiltPoint steps.1 i)
          (canonicalCompletedC3RadialTiltPoint steps.2 j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) =
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialTiltPoint steps.1 i)
          (canonicalCompletedC3RadialTiltPoint steps.2 j)

/-- On shrinking radial stencils, the abstract-looking boundary
intertwining is exactly the no-leak statement for the already channel-separated
Gamma/ledger defect.  Strip membership and nonvanishing are consequences of
approaching the nonzero Taylor center, not additional premises. -/
theorem
    canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_iff_ledgerNoLeak :
    CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining ↔
      CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  constructor
  · intro hboundary p q
    have hi : ∀ᶠ k : ℕ in atTop, ∀ i ∈ Finset.range (p + 1),
        canonicalCompletedC3RadialTiltPoint k i ∈
            completedNativeHeightDomain ∧
          completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 :=
      (Finset.range (p + 1)).eventually_all.2 fun i hi =>
        canonicalCompletedC3RadialTiltPoint_eventually_admissible i
    have hj : ∀ᶠ k : ℕ in atTop, ∀ j ∈ Finset.range (q + 1),
        canonicalCompletedC3RadialTiltPoint k j ∈
            completedNativeHeightDomain ∧
          completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 :=
      (Finset.range (q + 1)).eventually_all.2 fun j hj =>
        canonicalCompletedC3RadialTiltPoint_eventually_admissible j
    filter_upwards [hboundary p q, hfst.eventually hi, hsnd.eventually hj] with
      steps hsewing hiSteps hjSteps
    intro i hii j hjj
    have hz := hiSteps i hii
    have hw := hjSteps j hjj
    have hsep :
        canonicalCompletedC3RadialTiltPoint steps.2 j ≠
          conj (canonicalCompletedC3RadialTiltPoint steps.1 i) :=
      sub_ne_zero.mp
        (canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
          steps.1 steps.2 i j)
    rw [canonicalCompletedC3GammaLedgerBoundaryDefect, sub_eq_zero]
    calc
      canonicalCompletedC3PolarizedGammaBoundaryReadout
          (canonicalCompletedC3RadialTiltPoint steps.1 i)
          (canonicalCompletedC3RadialTiltPoint steps.2 j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) =
        (canonicalCompletedC3RadialTiltPoint steps.2 j -
            conj (canonicalCompletedC3RadialTiltPoint steps.1 i)) *
          canonicalCompletedNativePolarizedDslopeKernel
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j) :=
              hsewing i hii j hjj
      _ = canonicalCompletedC3AllCutoffPolarizedLedgerNumerator 0
          (canonicalCompletedC3RadialTiltPoint steps.1 i)
          (canonicalCompletedC3RadialTiltPoint steps.2 j) :=
            (canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
              0 hz.1 hw.1 hz.2 hw.2 hsep).symm
  · intro hnoLeak p q
    have hi : ∀ᶠ k : ℕ in atTop, ∀ i ∈ Finset.range (p + 1),
        canonicalCompletedC3RadialTiltPoint k i ∈
            completedNativeHeightDomain ∧
          completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 :=
      (Finset.range (p + 1)).eventually_all.2 fun i hi =>
        canonicalCompletedC3RadialTiltPoint_eventually_admissible i
    have hj : ∀ᶠ k : ℕ in atTop, ∀ j ∈ Finset.range (q + 1),
        canonicalCompletedC3RadialTiltPoint k j ∈
            completedNativeHeightDomain ∧
          completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 :=
      (Finset.range (q + 1)).eventually_all.2 fun j hj =>
        canonicalCompletedC3RadialTiltPoint_eventually_admissible j
    filter_upwards [hnoLeak p q, hfst.eventually hi, hsnd.eventually hj] with
      steps hdefect hiSteps hjSteps
    intro i hii j hjj
    have hz := hiSteps i hii
    have hw := hjSteps j hjj
    have hsep :
        canonicalCompletedC3RadialTiltPoint steps.2 j ≠
          conj (canonicalCompletedC3RadialTiltPoint steps.1 i) :=
      sub_ne_zero.mp
        (canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
          steps.1 steps.2 i j)
    have hledger :=
      canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
        0 hz.1 hw.1 hz.2 hw.2 hsep
    have hdef := hdefect i hii j hjj
    rw [canonicalCompletedC3GammaLedgerBoundaryDefect, sub_eq_zero] at hdef
    rw [← hledger]
    exact hdef

/-- The channel-separated ledger no-leak gate is exactly the local positive
Gamma-kernel realization.  This theorem discharges strip membership,
characteristic nonvanishing, and separation from the shrinking radial
geometry; it does not assume a global Green sewing. -/
theorem
    canonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak_iff_kernelIntertwining :
    CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak ↔
      CanonicalCompletedC3AsymptoticRadialGammaKernelIntertwining := by
  rw [←
    canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_iff_ledgerNoLeak]
  constructor
  · intro hboundary p q
    filter_upwards [hboundary p q] with steps hsteps
    intro i hi j hj
    exact
      (canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_boundaryReadout
        (canonicalCompletedC3RadialTiltPoint steps.1 i)
        (canonicalCompletedC3RadialTiltPoint steps.2 j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)
        (canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
          steps.1 steps.2 i j)).2
        (hsteps i hi j hj)
  · intro hkernel p q
    filter_upwards [hkernel p q] with steps hsteps
    intro i hi j hj
    exact
      (canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_boundaryReadout
        (canonicalCompletedC3RadialTiltPoint steps.1 i)
        (canonicalCompletedC3RadialTiltPoint steps.2 j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)
        (canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
          steps.1 steps.2 i j)).1
        (hsteps i hi j hj)

/-- A global radial numerator identity supplies its local asymptotic germ. -/
theorem canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_of_global
    (hboundary : CanonicalCompletedC3RadialTiltBoundaryIntertwining) :
    CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining := by
  intro p q
  filter_upwards with steps
  intro i hi j hj
  exact hboundary steps.1 steps.2 i j

/-- On every shifted radial sample rectangle, the total Gamma Gram is the
completed-native polarized `dslope` as soon as the division-free radial
boundary intertwining closes. -/
theorem canonicalCompletedC3TotalGammaKernel_eq_dslope_on_radialGrid
    (hboundary : CanonicalCompletedC3RadialTiltBoundaryIntertwining)
    (k l i j : ℕ) :
    inner ℂ
        (canonicalCompletedC3TotalGammaState
          (canonicalCompletedC3RadialTiltPoint k i))
        (canonicalCompletedC3TotalGammaState
          (canonicalCompletedC3RadialTiltPoint l j)) =
      canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint l j) := by
  rw [canonicalCompletedC3TotalGammaState_of_im_ne_zero
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i),
    canonicalCompletedC3TotalGammaState_of_im_ne_zero
      (canonicalCompletedC3RadialTiltPoint l j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero l j)]
  exact
    (canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_boundaryReadout
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint l j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero l j)
      (canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep k l i j)).2
      (hboundary k l i j)

/-- Concrete shifted radial Gamma jet of one derivative order. -/
def canonicalCompletedC3RadialGammaJet (k order : ℕ) :
    CarryGammaComplexNaimark :=
  completedGreenShiftedForwardDifferenceJet
    canonicalCompletedC3TotalGammaState
    (canonicalCompletedC3RadialSecondStep k) order

/-- Normalized all-order mismatch between the positive radial Gamma jets and
the completed-native `dslope` coefficient extractor.  Unlike the pointwise
boundary defect, this quantity retains only the exact germ seen by the
orders `(p,q)` at the centered height. -/
def canonicalCompletedC3RadialGammaDslopeJetDefect
    (steps : ℕ × ℕ) (p q : ℕ) : ℂ :=
  inner ℂ
      (canonicalCompletedC3RadialGammaJet steps.1 p)
      (canonicalCompletedC3RadialGammaJet steps.2 q) -
    completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep steps.1)
      (canonicalCompletedC3RadialSecondStep steps.2) p q

/-- The minimal all-order radial sewing gate: every normalized mixed jet of
the concrete Gamma/ledger mismatch vanishes at the centered germ.  It does
not require pointwise sewing on any neighborhood or at any characteristic
zero. -/
def CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness : Prop :=
  ∀ p q : ℕ,
    Tendsto
      (fun steps : ℕ × ℕ =>
        canonicalCompletedC3RadialGammaDslopeJetDefect steps p q)
      atTop (nhds 0)

/-- Quadratic energy mismatch for two independently refined radial jets.
The target retains all four entries of the corresponding two-vector
`dslope` form, so no mixed channel is discarded before polarization. -/
def canonicalCompletedC3RadialGammaDslopePairEnergyDefect
    (steps : ℕ × ℕ) (p q : ℕ) (a : ℂ) : ℂ :=
  let x := canonicalCompletedC3RadialGammaJet steps.1 p
  let y := canonicalCompletedC3RadialGammaJet steps.2 q
  let kernel := completedGreenKernelTwoStepShiftedForwardDifference
    canonicalCompletedNativePolarizedDslopeKernel
  inner ℂ (x + a • y) (x + a • y) -
    (kernel
        (canonicalCompletedC3RadialSecondStep steps.1)
        (canonicalCompletedC3RadialSecondStep steps.1) p p +
      a * kernel
        (canonicalCompletedC3RadialSecondStep steps.1)
        (canonicalCompletedC3RadialSecondStep steps.2) p q +
      conj a * kernel
        (canonicalCompletedC3RadialSecondStep steps.2)
        (canonicalCompletedC3RadialSecondStep steps.1) q p +
      conj a * a * kernel
        (canonicalCompletedC3RadialSecondStep steps.2)
        (canonicalCompletedC3RadialSecondStep steps.2) q q)

/-- The four canonical complex rotations are the exact quadratic-energy data
needed to reconstruct every mixed radial jet coefficient. -/
def CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness : Prop :=
  ∀ p q : ℕ,
    Tendsto
        (fun steps : ℕ × ℕ =>
          canonicalCompletedC3RadialGammaDslopePairEnergyDefect
            steps p q 1)
        atTop (nhds 0) ∧
      Tendsto
        (fun steps : ℕ × ℕ =>
          canonicalCompletedC3RadialGammaDslopePairEnergyDefect
            steps p q (-1))
        atTop (nhds 0) ∧
      Tendsto
        (fun steps : ℕ × ℕ =>
          canonicalCompletedC3RadialGammaDslopePairEnergyDefect
            steps p q Complex.I)
        atTop (nhds 0) ∧
      Tendsto
        (fun steps : ℕ × ℕ =>
          canonicalCompletedC3RadialGammaDslopePairEnergyDefect
            steps p q (-Complex.I))
        atTop (nhds 0)

/-- Complex polarization recovers the oriented mixed defect from the four
quadratic energy defects.  This is an algebraic identity at every pair of
cutoffs, not a limiting or positivity argument. -/
theorem canonicalCompletedC3RadialGammaDslopeJetDefect_eq_polarizedEnergy
    (steps : ℕ × ℕ) (p q : ℕ) :
    canonicalCompletedC3RadialGammaDslopeJetDefect steps p q =
      (canonicalCompletedC3RadialGammaDslopePairEnergyDefect
          steps p q 1 -
        canonicalCompletedC3RadialGammaDslopePairEnergyDefect
          steps p q (-1) -
        Complex.I *
          canonicalCompletedC3RadialGammaDslopePairEnergyDefect
            steps p q Complex.I +
        Complex.I *
          canonicalCompletedC3RadialGammaDslopePairEnergyDefect
            steps p q (-Complex.I)) / 4 := by
  unfold canonicalCompletedC3RadialGammaDslopePairEnergyDefect
    canonicalCompletedC3RadialGammaDslopeJetDefect
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, map_one, one_mul, map_neg,
    Complex.conj_I, neg_mul, mul_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Expanding one quadratic energy mismatch gives the four oriented jet
defects, including both cross orientations and both diagonal channels. -/
theorem canonicalCompletedC3RadialGammaDslopePairEnergyDefect_eq_jetDefects
    (steps : ℕ × ℕ) (p q : ℕ) (a : ℂ) :
    canonicalCompletedC3RadialGammaDslopePairEnergyDefect steps p q a =
      canonicalCompletedC3RadialGammaDslopeJetDefect
          (steps.1, steps.1) p p +
        a * canonicalCompletedC3RadialGammaDslopeJetDefect steps p q +
        conj a * canonicalCompletedC3RadialGammaDslopeJetDefect
          (steps.2, steps.1) q p +
        conj a * a * canonicalCompletedC3RadialGammaDslopeJetDefect
          (steps.2, steps.2) q q := by
  unfold canonicalCompletedC3RadialGammaDslopePairEnergyDefect
    canonicalCompletedC3RadialGammaDslopeJetDefect
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right]
  ring

/-- Convergence of the four uncollapsed quadratic energies closes the full
mixed all-order sewing by polarization. -/
theorem
    canonicalCompletedC3RadialGammaDslopeJetDefectFlatness_of_quadraticEnergy
    (henergy :
      CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness) :
    CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness := by
  intro p q
  obtain ⟨hOne, hNegOne, hI, hNegI⟩ := henergy p q
  have hpolarized :=
    (((hOne.sub hNegOne).sub (hI.const_mul Complex.I)).add
      (hNegI.const_mul Complex.I)).div_const (4 : ℂ)
  convert hpolarized using 1
  · funext steps
    exact
      (canonicalCompletedC3RadialGammaDslopeJetDefect_eq_polarizedEnergy
        steps p q)
  · norm_num

/-- Conversely, mixed jet flatness makes every quadratic combination flat.
Thus the energy formulation is exactly equivalent to the original mixed
gate, rather than a stronger hidden assumption. -/
theorem
    canonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness_of_jetDefect
    (hflat : CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness) :
    CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hdiagFst : Tendsto (fun steps : ℕ × ℕ => (steps.1, steps.1))
      atTop atTop := by
    simpa only [prod_atTop_atTop_eq] using hfst.prodMk hfst
  have hswap : Tendsto (fun steps : ℕ × ℕ => (steps.2, steps.1))
      atTop atTop := by
    simpa only [prod_atTop_atTop_eq] using hsnd.prodMk hfst
  have hdiagSnd : Tendsto (fun steps : ℕ × ℕ => (steps.2, steps.2))
      atTop atTop := by
    simpa only [prod_atTop_atTop_eq] using hsnd.prodMk hsnd
  intro p q
  have henergy (a : ℂ) :
      Tendsto
        (fun steps : ℕ × ℕ =>
          canonicalCompletedC3RadialGammaDslopePairEnergyDefect
            steps p q a)
        atTop (nhds 0) := by
    have hpp := (hflat p p).comp hdiagFst
    have hpq := hflat p q
    have hqp := (hflat q p).comp hswap
    have hqq := (hflat q q).comp hdiagSnd
    have hsum :=
      (((hpp.add (hpq.const_mul a)).add (hqp.const_mul (conj a))).add
        (hqq.const_mul (conj a * a)))
    convert hsum using 1
    · funext steps
      exact
        (canonicalCompletedC3RadialGammaDslopePairEnergyDefect_eq_jetDefects
          steps p q a)
    · norm_num
  exact ⟨henergy 1, henergy (-1), henergy Complex.I,
    henergy (-Complex.I)⟩

/-- Exact energy-level characterization of the radial all-order sewing. -/
theorem
    canonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness_iff :
    CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness ↔
      CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness :=
  ⟨canonicalCompletedC3RadialGammaDslopeJetDefectFlatness_of_quadraticEnergy,
    canonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness_of_jetDefect⟩

/-- At order zero the shifted jet is the concrete off-axis Gamma state and
the coefficient extractor is the un-differenced polarized `dslope`.  This is
the first scalar energy comparison required by the quadratic route. -/
theorem canonicalCompletedC3RadialGammaDslopeJetDefect_zero_zero
    (steps : ℕ × ℕ) :
    canonicalCompletedC3RadialGammaDslopeJetDefect steps 0 0 =
      inner ℂ
          (canonicalCompletedC3TotalGammaState
            (canonicalCompletedC3RadialSecondStep steps.1))
          (canonicalCompletedC3TotalGammaState
            (canonicalCompletedC3RadialSecondStep steps.2)) -
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) := by
  unfold canonicalCompletedC3RadialGammaDslopeJetDefect
    canonicalCompletedC3RadialGammaJet
    completedGreenShiftedForwardDifferenceJet
    completedGreenKernelTwoStepShiftedForwardDifference
    completedGreenKernelTwoStepShiftedRawDifference
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, one_mul, inv_one,
    one_smul, Function.iterate_zero_apply, map_one]

@[simp] theorem canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep
    (k : ℕ) :
    canonicalCompletedC3RadialTiltPoint k 0 =
      canonicalCompletedC3RadialSecondStep k := by
  simpa using canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul k 0

/-- At order zero the division-free Gamma/ledger boundary defect is exactly
the spectral separation times the Gamma/`dslope` jet defect.  Hence the
correct boundary target near the centered collision is first-order no-leak,
not mere convergence of the unnormalized boundary defect to zero. -/
theorem
    canonicalCompletedC3RadialGammaLedgerBoundaryDefect_eq_separation_mul_zeroJetDefect
    (M : ℕ) (steps : ℕ × ℕ)
    (hzStrip : canonicalCompletedC3RadialSecondStep steps.1 ∈
      completedNativeHeightDomain)
    (hwStrip : canonicalCompletedC3RadialSecondStep steps.2 ∈
      completedNativeHeightDomain)
    (hzF : completedNativeOperatorCharacteristic
        (canonicalCompletedC3RadialSecondStep steps.1) ≠ 0)
    (hwF : completedNativeOperatorCharacteristic
        (canonicalCompletedC3RadialSecondStep steps.2) ≠ 0) :
    canonicalCompletedC3GammaLedgerBoundaryDefect M
        (canonicalCompletedC3RadialSecondStep steps.1)
        (canonicalCompletedC3RadialSecondStep steps.2)
        (by
          simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
            using canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 0)
        (by
          simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
            using canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 0) =
      (canonicalCompletedC3RadialSecondStep steps.2 -
          conj (canonicalCompletedC3RadialSecondStep steps.1)) *
        canonicalCompletedC3RadialGammaDslopeJetDefect steps 0 0 := by
  have hz : (canonicalCompletedC3RadialSecondStep steps.1).im ≠ 0 := by
    simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
      using canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 0
  have hw : (canonicalCompletedC3RadialSecondStep steps.2).im ≠ 0 := by
    simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
      using canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 0
  have hsep : canonicalCompletedC3RadialSecondStep steps.2 ≠
      conj (canonicalCompletedC3RadialSecondStep steps.1) := by
    apply sub_ne_zero.mp
    simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep] using
      canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
        steps.1 steps.2 0 0
  rw [canonicalCompletedC3GammaLedgerBoundaryDefect,
    canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel,
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
      M hzStrip hwStrip hzF hwF hsep,
    canonicalCompletedC3RadialGammaDslopeJetDefect_zero_zero]
  rw [canonicalCompletedC3TotalGammaState_of_im_ne_zero
      (z := canonicalCompletedC3RadialSecondStep steps.1) hz,
    canonicalCompletedC3TotalGammaState_of_im_ne_zero
      (z := canonicalCompletedC3RadialSecondStep steps.2) hw]
  unfold canonicalCompletedC3PolarizedGammaKernel
  ring

/-- First-order normalized boundary mismatch on the shrinking order-zero
radial pair.  The denominator is the intrinsic Gamma Green separation and is
nonzero at every finite pair of radial steps. -/
def canonicalCompletedC3RadialGammaLedgerNormalizedZeroBoundaryDefect
    (steps : ℕ × ℕ) : ℂ :=
  canonicalCompletedC3GammaLedgerBoundaryDefect 0
      (canonicalCompletedC3RadialTiltPoint steps.1 0)
      (canonicalCompletedC3RadialTiltPoint steps.2 0)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 0)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 0) /
    (canonicalCompletedC3RadialTiltPoint steps.2 0 -
      conj (canonicalCompletedC3RadialTiltPoint steps.1 0))

/-- The normalized order-zero boundary mismatch is eventually literally the
order-zero Gamma/`dslope` jet defect.  Admissibility and nonvanishing follow
from approach to the nonzero completed-native center. -/
theorem
    canonicalCompletedC3RadialGammaLedgerNormalizedZeroBoundaryDefect_eventually_eq :
    (fun steps : ℕ × ℕ =>
      canonicalCompletedC3RadialGammaLedgerNormalizedZeroBoundaryDefect steps) =ᶠ[atTop]
      (fun steps : ℕ × ℕ =>
        canonicalCompletedC3RadialGammaDslopeJetDefect steps 0 0) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hadmissible := canonicalCompletedC3RadialTiltPoint_eventually_admissible 0
  filter_upwards [hfst.eventually hadmissible, hsnd.eventually hadmissible] with
    steps hz hw
  have hsep : canonicalCompletedC3RadialTiltPoint steps.2 0 -
      conj (canonicalCompletedC3RadialTiltPoint steps.1 0) ≠ 0 :=
    canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
      steps.1 steps.2 0 0
  have hboundary :=
    canonicalCompletedC3RadialGammaLedgerBoundaryDefect_eq_separation_mul_zeroJetDefect
      0 steps (by simpa using hz.1) (by simpa using hw.1)
        (by simpa using hz.2) (by simpa using hw.2)
  unfold canonicalCompletedC3RadialGammaLedgerNormalizedZeroBoundaryDefect
  simp only [canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep] at hsep ⊢
  rw [hboundary]
  exact mul_div_cancel_left₀ _ hsep

/-- Exact order-zero boundary formulation of the first radial energy gate:
the boundary mismatch must vanish after division by its own spectral
separation. -/
theorem
    canonicalCompletedC3RadialGammaLedgerNormalizedZeroBoundaryDefect_tendsto_zero_iff :
    Tendsto
        canonicalCompletedC3RadialGammaLedgerNormalizedZeroBoundaryDefect
        atTop (nhds 0) ↔
      Tendsto
        (fun steps : ℕ × ℕ =>
          canonicalCompletedC3RadialGammaDslopeJetDefect steps 0 0)
        atTop (nhds 0) := by
  constructor <;> intro h
  · exact h.congr'
      canonicalCompletedC3RadialGammaLedgerNormalizedZeroBoundaryDefect_eventually_eq
  · exact h.congr'
      canonicalCompletedC3RadialGammaLedgerNormalizedZeroBoundaryDefect_eventually_eq.symm

/-- Flatness of the normalized defect is already sufficient to identify
every Gamma jet Gram coefficient with the canonical completed-native moment.
-/
theorem canonicalCompletedC3RadialGammaJet_inner_tendsto_of_defectFlatness
    (hflat : CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness)
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ => inner ℂ
        (canonicalCompletedC3RadialGammaJet steps.1 p)
        (canonicalCompletedC3RadialGammaJet steps.2 q))
      atTop
      (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q)) := by
  have hdefect := hflat p q
  have hdslope := completedNativePolarizedDslope_shiftedRadial_tendsto p q
  have hsum := hdefect.add hdslope
  simpa [canonicalCompletedC3RadialGammaDslopeJetDefect] using hsum

/-- Under the radial division-free boundary intertwining, the cross inner
products of the concrete Gamma jets converge to every canonical polarized
moment coefficient. -/
theorem canonicalCompletedC3RadialGammaJet_inner_tendsto_of_asymptotic
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ => inner ℂ
        (canonicalCompletedC3RadialGammaJet steps.1 p)
        (canonicalCompletedC3RadialGammaJet steps.2 q))
      atTop
      (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q)) := by
  have hlimit := completedNativePolarizedDslope_shiftedRadial_tendsto p q
  apply hlimit.congr'
  filter_upwards [hboundary p q] with steps hsteps
  symm
  change inner ℂ
      (completedGreenShiftedForwardDifferenceJet
        canonicalCompletedC3TotalGammaState
        (canonicalCompletedC3RadialSecondStep steps.1) p)
      (completedGreenShiftedForwardDifferenceJet
        canonicalCompletedC3TotalGammaState
        (canonicalCompletedC3RadialSecondStep steps.2) q) = _
  rw [inner_completedGreenShiftedForwardDifferenceJet_eq_kernel]
  apply completedGreenKernelTwoStepShiftedForwardDifference_eq_of_eq_on_grid
  intro i hi j hj
  rw [← canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul,
    ← canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  rw [canonicalCompletedC3TotalGammaState_of_im_ne_zero
      (canonicalCompletedC3RadialTiltPoint steps.1 i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i),
    canonicalCompletedC3TotalGammaState_of_im_ne_zero
      (canonicalCompletedC3RadialTiltPoint steps.2 j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)]
  exact
    (canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_boundaryReadout
      (canonicalCompletedC3RadialTiltPoint steps.1 i)
      (canonicalCompletedC3RadialTiltPoint steps.2 j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)
      (canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
        steps.1 steps.2 i j)).2
      (hsteps i hi j hj)

/-- The formerly used eventual pointwise boundary sewing implies the weaker
and exact all-order jet-flatness gate. -/
theorem
    canonicalCompletedC3RadialGammaDslopeJetDefectFlatness_of_asymptoticBoundary
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining) :
    CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness := by
  intro p q
  have hgamma :=
    canonicalCompletedC3RadialGammaJet_inner_tendsto_of_asymptotic
      hboundary p q
  have hdslope := completedNativePolarizedDslope_shiftedRadial_tendsto p q
  have hsub := hgamma.sub hdslope
  simpa [canonicalCompletedC3RadialGammaDslopeJetDefect] using hsub

/-- Exact audit of the local gate: defect flatness is equivalent to the
complete all-order Gamma Gram/moment identification. -/
theorem
    canonicalCompletedC3RadialGammaDslopeJetDefectFlatness_iff_inner_tendsto :
    CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness ↔
      ∀ p q : ℕ,
        Tendsto
          (fun steps : ℕ × ℕ => inner ℂ
            (canonicalCompletedC3RadialGammaJet steps.1 p)
            (canonicalCompletedC3RadialGammaJet steps.2 q))
          atTop
          (nhds (polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment p q)) := by
  constructor
  · intro hflat p q
    exact
      canonicalCompletedC3RadialGammaJet_inner_tendsto_of_defectFlatness
        hflat p q
  · intro hmoment p q
    have hgamma := hmoment p q
    have hdslope := completedNativePolarizedDslope_shiftedRadial_tendsto p q
    have hsub := hgamma.sub hdslope
    simpa [canonicalCompletedC3RadialGammaDslopeJetDefect] using hsub

/-- Global radial sewing is a sufficient, but deliberately stronger, input
for the same coefficient limit. -/
theorem canonicalCompletedC3RadialGammaJet_inner_tendsto
    (hboundary : CanonicalCompletedC3RadialTiltBoundaryIntertwining)
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ => inner ℂ
        (canonicalCompletedC3RadialGammaJet steps.1 p)
        (canonicalCompletedC3RadialGammaJet steps.2 q))
      atTop
      (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q)) :=
  canonicalCompletedC3RadialGammaJet_inner_tendsto_of_asymptotic
    (canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_of_global
      hboundary) p q

/-- Real part of a finite complex Gamma Gram is positive semidefinite: it is
the Gram matrix of the same vectors after canonical restriction of scalars. -/
theorem canonicalCompletedC3RadialGammaJet_realGram_posSemidef
    {ι : Type*} [Finite ι] (k : ℕ) (order : ι → ℕ) :
    (Matrix.of fun i j =>
      (inner ℂ
        (canonicalCompletedC3RadialGammaJet k (order i))
        (canonicalCompletedC3RadialGammaJet k (order j))).re).PosSemidef := by
  letI : NormedSpace ℝ CarryGammaComplexNaimark :=
    NormedSpace.restrictScalars ℝ ℂ CarryGammaComplexNaimark
  letI : InnerProductSpace ℝ CarryGammaComplexNaimark :=
    InnerProductSpace.rclikeToReal ℂ CarryGammaComplexNaimark
  change (Matrix.gram ℝ (fun i =>
    canonicalCompletedC3RadialGammaJet k (order i))).PosSemidef
  exact Matrix.posSemidef_gram ℝ _

/-- Even radial Gamma Gram at one common shrinking step. -/
def canonicalCompletedC3RadialGammaEvenGram (k N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    (inner ℂ
      (canonicalCompletedC3RadialGammaJet k (2 * (i : ℕ)))
      (canonicalCompletedC3RadialGammaJet k (2 * (j : ℕ)))).re

/-- Odd radial Gamma Gram at one common shrinking step. -/
def canonicalCompletedC3RadialGammaOddGram (k N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    (inner ℂ
      (canonicalCompletedC3RadialGammaJet k (2 * (i : ℕ) + 1))
      (canonicalCompletedC3RadialGammaJet k (2 * (j : ℕ) + 1))).re

theorem canonicalCompletedC3RadialGammaEvenGram_posSemidef (k N : ℕ) :
    (canonicalCompletedC3RadialGammaEvenGram k N).PosSemidef := by
  exact canonicalCompletedC3RadialGammaJet_realGram_posSemidef
    k (fun i : Fin N => 2 * (i : ℕ))

theorem canonicalCompletedC3RadialGammaOddGram_posSemidef (k N : ℕ) :
    (canonicalCompletedC3RadialGammaOddGram k N).PosSemidef := by
  exact canonicalCompletedC3RadialGammaJet_realGram_posSemidef
    k (fun i : Fin N => 2 * (i : ℕ) + 1)

/-- Under the local radial boundary germ, the complete even Gamma matrices
converge entrywise to the canonical completed-native Hankel matrices. -/
theorem canonicalCompletedC3RadialGammaEvenGram_tendsto
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (N : ℕ) :
    Tendsto
      (fun k : ℕ => canonicalCompletedC3RadialGammaEvenGram k N)
      atTop
      (nhds (hankelGram canonicalCompletedNativeLogDerivativeMoment N)) := by
  change Tendsto
    (fun k i j => canonicalCompletedC3RadialGammaEvenGram k N i j)
    atTop
    (nhds (fun i j =>
      hankelGram canonicalCompletedNativeLogDerivativeMoment N i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hdiag : Tendsto (fun k : ℕ => (k, k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  have hcomplex :=
    (canonicalCompletedC3RadialGammaJet_inner_tendsto_of_asymptotic
      hboundary (2 * (i : ℕ)) (2 * (j : ℕ))).comp hdiag
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  simpa [canonicalCompletedC3RadialGammaEvenGram, Function.comp_def,
    hankelGram, completedGreenParityOrder,
    greenWronskianMomentKernel] using hreal

/-- The odd Gamma matrices converge to the shifted completed-native Hankel
matrices under the same local radial boundary germ. -/
theorem canonicalCompletedC3RadialGammaOddGram_tendsto
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (N : ℕ) :
    Tendsto
      (fun k : ℕ => canonicalCompletedC3RadialGammaOddGram k N)
      atTop
      (nhds (shiftedHankel
        canonicalCompletedNativeLogDerivativeMoment N)) := by
  change Tendsto
    (fun k i j => canonicalCompletedC3RadialGammaOddGram k N i j)
    atTop
    (nhds (fun i j => shiftedHankel
      canonicalCompletedNativeLogDerivativeMoment N i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hdiag : Tendsto (fun k : ℕ => (k, k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  have hcomplex :=
    (canonicalCompletedC3RadialGammaJet_inner_tendsto_of_asymptotic
      hboundary (2 * (i : ℕ) + 1) (2 * (j : ℕ) + 1)).comp hdiag
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  simpa [canonicalCompletedC3RadialGammaOddGram, Function.comp_def,
    shiftedHankel, completedGreenParityOrder,
    greenWronskianMomentKernel] using hreal

/-- Determinants pass through the finite-dimensional Gamma-to-Hankel limit. -/
theorem canonicalCompletedC3RadialGammaEvenGram_det_tendsto
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (N : ℕ) :
    Tendsto
      (fun k : ℕ => (canonicalCompletedC3RadialGammaEvenGram k N).det)
      atTop
      (nhds (hankelGram
        canonicalCompletedNativeLogDerivativeMoment N).det) := by
  exact (Continuous.matrix_det continuous_id).continuousAt.tendsto.comp
    (canonicalCompletedC3RadialGammaEvenGram_tendsto hboundary N)

theorem canonicalCompletedC3RadialGammaOddGram_det_tendsto
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (N : ℕ) :
    Tendsto
      (fun k : ℕ => (canonicalCompletedC3RadialGammaOddGram k N).det)
      atTop
      (nhds (shiftedHankel
        canonicalCompletedNativeLogDerivativeMoment N).det) := by
  exact (Continuous.matrix_det continuous_id).continuousAt.tendsto.comp
    (canonicalCompletedC3RadialGammaOddGram_tendsto hboundary N)

/-- Geometric no-collapse condition at one fixed finite order. -/
def CanonicalCompletedC3RadialGammaDeterminantLowerBoundAt (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ᶠ k : ℕ in atTop,
      c ≤ (canonicalCompletedC3RadialGammaEvenGram k N).det) ∧
    (∀ᶠ k : ℕ in atTop,
      c ≤ (canonicalCompletedC3RadialGammaOddGram k N).det)

/-- Geometric no-collapse condition for radial tilt.  It asks for a positive
lower determinant bound at each fixed finite order, uniform only in the
shrinking radial step. -/
def CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound : Prop :=
  ∀ N : ℕ, CanonicalCompletedC3RadialGammaDeterminantLowerBoundAt N

/-- The empty Gram section cannot collapse. -/
theorem canonicalCompletedC3RadialGammaDeterminantLowerBoundAt_zero :
    CanonicalCompletedC3RadialGammaDeterminantLowerBoundAt 0 := by
  refine ⟨1, by norm_num, ?_, ?_⟩
  · filter_upwards with k
    simp [canonicalCompletedC3RadialGammaEvenGram]
  · filter_upwards with k
    simp [canonicalCompletedC3RadialGammaOddGram]

/-- The first nontrivial no-collapse test is exactly a uniform lower bound
for the squared-norm readouts of radial Gamma jets of orders zero and one. -/
theorem canonicalCompletedC3RadialGammaDeterminantLowerBoundAt_one_iff :
    CanonicalCompletedC3RadialGammaDeterminantLowerBoundAt 1 ↔
      ∃ c : ℝ, 0 < c ∧
        (∀ᶠ k : ℕ in atTop,
          c ≤ (inner ℂ
            (canonicalCompletedC3RadialGammaJet k 0)
            (canonicalCompletedC3RadialGammaJet k 0)).re) ∧
        (∀ᶠ k : ℕ in atTop,
          c ≤ (inner ℂ
            (canonicalCompletedC3RadialGammaJet k 1)
            (canonicalCompletedC3RadialGammaJet k 1)).re) := by
  simp only [CanonicalCompletedC3RadialGammaDeterminantLowerBoundAt,
    canonicalCompletedC3RadialGammaEvenGram,
    canonicalCompletedC3RadialGammaOddGram, Matrix.det_fin_one,
    Matrix.of_apply, Fin.val_zero, mul_zero, zero_add]

/-- Once the radial kernel coefficients have been identified, a uniform
geometric determinant bound is neither weaker nor stronger than strict
positivity of the two limiting determinants.  This prevents using the
no-collapse gate as a disguised assumption about the answer. -/
theorem canonicalCompletedC3RadialGammaDeterminantLowerBoundAt_iff_limit_det_pos
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (N : ℕ) :
    CanonicalCompletedC3RadialGammaDeterminantLowerBoundAt N ↔
      0 < (hankelGram
        canonicalCompletedNativeLogDerivativeMoment N).det ∧
      0 < (shiftedHankel
        canonicalCompletedNativeLogDerivativeMoment N).det := by
  constructor
  · rintro ⟨c, hc, heven, hodd⟩
    constructor
    · have hle : c ≤
          (hankelGram canonicalCompletedNativeLogDerivativeMoment N).det :=
        ge_of_tendsto
          (canonicalCompletedC3RadialGammaEvenGram_det_tendsto hboundary N)
          heven
      exact hc.trans_le hle
    · have hle : c ≤
          (shiftedHankel
            canonicalCompletedNativeLogDerivativeMoment N).det :=
        ge_of_tendsto
          (canonicalCompletedC3RadialGammaOddGram_det_tendsto hboundary N)
          hodd
      exact hc.trans_le hle
  · rintro ⟨hevenPos, hoddPos⟩
    let evenDet : ℝ :=
      (hankelGram canonicalCompletedNativeLogDerivativeMoment N).det
    let oddDet : ℝ :=
      (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N).det
    let c : ℝ := min evenDet oddDet / 2
    have hminPos : 0 < min evenDet oddDet :=
      lt_min (by simpa [evenDet] using hevenPos)
        (by simpa [oddDet] using hoddPos)
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hcEven : c < evenDet := by
      dsimp [c]
      have hle := min_le_left evenDet oddDet
      linarith
    have hcOdd : c < oddDet := by
      dsimp [c]
      have hle := min_le_right evenDet oddDet
      linarith
    refine ⟨c, hc, ?_, ?_⟩
    · have heventually : ∀ᶠ k : ℕ in atTop,
          c < (canonicalCompletedC3RadialGammaEvenGram k N).det :=
        (canonicalCompletedC3RadialGammaEvenGram_det_tendsto hboundary N).eventually
          (Ioi_mem_nhds (by simpa [evenDet] using hcEven))
      filter_upwards [heventually] with k hk
      exact hk.le
    · have heventually : ∀ᶠ k : ℕ in atTop,
          c < (canonicalCompletedC3RadialGammaOddGram k N).det :=
        (canonicalCompletedC3RadialGammaOddGram_det_tendsto hboundary N).eventually
          (Ioi_mem_nhds (by simpa [oddDet] using hcOdd))
      filter_upwards [heventually] with k hk
      exact hk.le

/-- All-order version of the preceding exact audit. -/
theorem canonicalCompletedC3RadialGammaUniformDeterminantLowerBound_iff
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining) :
    CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound ↔
      ∀ N : ℕ,
        0 < (hankelGram
          canonicalCompletedNativeLogDerivativeMoment N).det ∧
        0 < (shiftedHankel
          canonicalCompletedNativeLogDerivativeMoment N).det := by
  constructor
  · intro hstrict N
    exact
      (canonicalCompletedC3RadialGammaDeterminantLowerBoundAt_iff_limit_det_pos
        hboundary N).1 (hstrict N)
  · intro hdet N
    exact
      (canonicalCompletedC3RadialGammaDeterminantLowerBoundAt_iff_limit_det_pos
        hboundary N).2 (hdet N)

/-- Uniform finite-order Pythagorean non-collapse is exactly strong enough to
prevent the two limiting Hankel towers from losing rank. -/
theorem canonicalCompletedNativeHankelPairNondegenerate_of_radialGamma
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound) :
    CanonicalCompletedNativeHankelPairNondegenerate := by
  intro N
  obtain ⟨c, hc, heven, hodd⟩ := hstrict N
  constructor
  · have hle : c ≤
        (hankelGram canonicalCompletedNativeLogDerivativeMoment N).det :=
      ge_of_tendsto
        (canonicalCompletedC3RadialGammaEvenGram_det_tendsto hboundary N)
        heven
    exact ne_of_gt (hc.trans_le hle)
  · have hle : c ≤
        (shiftedHankel
          canonicalCompletedNativeLogDerivativeMoment N).det :=
      ge_of_tendsto
        (canonicalCompletedC3RadialGammaOddGram_det_tendsto hboundary N)
        hodd
    exact ne_of_gt (hc.trans_le hle)

/-- Flatness of the all-order radial defect supplies both completed-native
Hankel towers as closed positive forms.  No pointwise boundary sewing is used
in this coefficient-level statement. -/
theorem
    canonicalCompletedNativeStieltjesPosSemidefinite_of_radialGammaDslopeJetDefectFlatness
    (hflat : CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness) :
    CanonicalCompletedNativeStieltjesPosSemidefinite := by
  intro N
  have hdiag : Tendsto (fun k : ℕ => (k, k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  constructor
  · let evenGram (k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
      Matrix.of fun i j =>
        (inner ℂ
          (canonicalCompletedC3RadialGammaJet k (2 * (i : ℕ)))
          (canonicalCompletedC3RadialGammaJet k (2 * (j : ℕ)))).re
    apply matrixPosSemidef_of_tendsto_entrywise
        (A := evenGram)
    · intro k
      exact canonicalCompletedC3RadialGammaJet_realGram_posSemidef
        k (fun i : Fin N => 2 * (i : ℕ))
    · intro i j
      have hcomplex :=
        (canonicalCompletedC3RadialGammaJet_inner_tendsto_of_defectFlatness
          hflat (2 * (i : ℕ)) (2 * (j : ℕ))).comp hdiag
      have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
      simpa [evenGram, Function.comp_def, hankelGram,
        completedGreenParityOrder, greenWronskianMomentKernel] using hreal
  · let oddGram (k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
      Matrix.of fun i j =>
        (inner ℂ
          (canonicalCompletedC3RadialGammaJet k (2 * (i : ℕ) + 1))
          (canonicalCompletedC3RadialGammaJet k (2 * (j : ℕ) + 1))).re
    apply matrixPosSemidef_of_tendsto_entrywise
        (A := oddGram)
    · intro k
      exact canonicalCompletedC3RadialGammaJet_realGram_posSemidef
        k (fun i : Fin N => 2 * (i : ℕ) + 1)
    · intro i j
      have hcomplex :=
        (canonicalCompletedC3RadialGammaJet_inner_tendsto_of_defectFlatness
          hflat (2 * (i : ℕ) + 1) (2 * (j : ℕ) + 1)).comp hdiag
      have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
      simpa [oddGram, Function.comp_def, shiftedHankel,
        completedGreenParityOrder, greenWronskianMomentKernel] using hreal

/-- The four quadratic tilt-energy limits already supply both completed
Hankel towers as positive semidefinite forms. -/
theorem
    canonicalCompletedNativeStieltjesPosSemidefinite_of_radialGammaQuadraticEnergy
    (henergy :
      CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness) :
    CanonicalCompletedNativeStieltjesPosSemidefinite :=
  canonicalCompletedNativeStieltjesPosSemidefinite_of_radialGammaDslopeJetDefectFlatness
    (canonicalCompletedC3RadialGammaDslopeJetDefectFlatness_of_quadraticEnergy
      henergy)

/-- The earlier local pointwise boundary germ is a sufficient source of the
minimal jet-flatness input. -/
theorem
    canonicalCompletedNativeStieltjesPosSemidefinite_of_asymptoticRadialTiltBoundary
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining) :
    CanonicalCompletedNativeStieltjesPosSemidefinite :=
  canonicalCompletedNativeStieltjesPosSemidefinite_of_radialGammaDslopeJetDefectFlatness
    (canonicalCompletedC3RadialGammaDslopeJetDefectFlatness_of_asymptoticBoundary
      hboundary)

/-- Global radial sewing implies the same all-order semidefinite conclusion
through its asymptotic germ. -/
theorem canonicalCompletedNativeStieltjesPosSemidefinite_of_radialTiltBoundary
    (hboundary : CanonicalCompletedC3RadialTiltBoundaryIntertwining) :
    CanonicalCompletedNativeStieltjesPosSemidefinite :=
  canonicalCompletedNativeStieltjesPosSemidefinite_of_asymptoticRadialTiltBoundary
    (canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_of_global
      hboundary)

/-- Adding the already isolated finite nondegeneracy gate upgrades the local
radial tilt germ to the exact strict Stieltjes positivity required by the
canonical HP operator. -/
theorem
    canonicalCompletedNativeStieltjesPositivity_of_radialGammaDslopeJetDefectFlatness
    (hflat : CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeStieltjesPositivity := by
  rw [
    canonicalCompletedNativeStieltjesPositivity_iff_posSemidefinite_and_nondegenerate]
  exact
    ⟨canonicalCompletedNativeStieltjesPosSemidefinite_of_radialGammaDslopeJetDefectFlatness
        hflat,
      hnondegenerate⟩

/-- Quadratic tilt-energy sewing plus the separately isolated no-collapse
gate gives the strict Stieltjes positivity required by the HP operator. -/
theorem
    canonicalCompletedNativeStieltjesPositivity_of_radialGammaQuadraticEnergy
    (henergy :
      CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeStieltjesPositivity :=
  canonicalCompletedNativeStieltjesPositivity_of_radialGammaDslopeJetDefectFlatness
    (canonicalCompletedC3RadialGammaDslopeJetDefectFlatness_of_quadraticEnergy
      henergy)
    hnondegenerate

/-- The earlier boundary-germ spelling factors through jet flatness. -/
theorem
    canonicalCompletedNativeStieltjesPositivity_of_asymptoticRadialTiltBoundary
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeStieltjesPositivity :=
  canonicalCompletedNativeStieltjesPositivity_of_radialGammaDslopeJetDefectFlatness
    (canonicalCompletedC3RadialGammaDslopeJetDefectFlatness_of_asymptoticBoundary
      hboundary)
    hnondegenerate

/-- The stronger global radial sewing has the same strict consequence. -/
theorem canonicalCompletedNativeStieltjesPositivity_of_radialTiltBoundary
    (hboundary : CanonicalCompletedC3RadialTiltBoundaryIntertwining)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeStieltjesPositivity :=
  canonicalCompletedNativeStieltjesPositivity_of_asymptoticRadialTiltBoundary
    (canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_of_global
      hboundary)
    hnondegenerate

/-- Entirely radial formulation of strict Stieltjes positivity: local
boundary identification supplies the limiting Gram, while the uniform Gamma
determinant bound prevents rank loss. -/
theorem canonicalCompletedNativeStieltjesPositivity_of_radialGamma
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound) :
    CanonicalCompletedNativeStieltjesPositivity :=
  canonicalCompletedNativeStieltjesPositivity_of_asymptoticRadialTiltBoundary
    hboundary
    (canonicalCompletedNativeHankelPairNondegenerate_of_radialGamma
      hboundary hstrict)

/-- Channel-level spelling of the radial result.  The first premise is the
explicit no-leak condition for the completed C3 ledger, rather than a free
kernel or boundary equality. -/
theorem canonicalCompletedNativeStieltjesPositivity_of_radialLedger
    (hnoLeak : CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound) :
    CanonicalCompletedNativeStieltjesPositivity :=
  canonicalCompletedNativeStieltjesPositivity_of_radialGamma
    (canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_iff_ledgerNoLeak.mpr
      hnoLeak)
    hstrict

/-- Exact logical audit of the two radial gates.  Once the channel-separated
Gamma/ledger no-leak identifies the limiting Gram, the uniform determinant
bound is precisely the remaining strict Stieltjes assertion.  In particular,
it cannot be recovered from finite positive semidefiniteness or entrywise
convergence alone. -/
theorem canonicalCompletedC3RadialGammaGates_iff_stieltjesPositivity :
    (CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak ∧
        CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound) ↔
      (CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak ∧
        CanonicalCompletedNativeStieltjesPositivity) := by
  constructor
  · rintro ⟨hnoLeak, hstrict⟩
    exact
      ⟨hnoLeak,
        canonicalCompletedNativeStieltjesPositivity_of_radialLedger
          hnoLeak hstrict⟩
  · rintro ⟨hnoLeak, hpos⟩
    refine ⟨hnoLeak, ?_⟩
    have hboundary :
        CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining :=
      canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_iff_ledgerNoLeak.mpr
        hnoLeak
    apply
      (canonicalCompletedC3RadialGammaUniformDeterminantLowerBound_iff
        hboundary).2
    intro N
    exact ⟨(hpos N).1.det_pos, (hpos N).2.det_pos⟩

/-- Local radial boundary intertwining plus finite nondegeneracy instantiates
the canonical completed-native HP carrier. -/
theorem
    completedNativeRealHPCarrierCertificate_of_radialGammaDslopeJetDefectFlatness
    (hflat : CanonicalCompletedC3RadialGammaDslopeJetDefectFlatness)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet
        (canonicalCompletedNativeStieltjesPositivity_of_radialGammaDslopeJetDefectFlatness
          hflat hnondegenerate)) :=
  completedNativeRealHPCarrierCertificate_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialGammaDslopeJetDefectFlatness
      hflat hnondegenerate)

/-- Direct HP certificate from the polarized quadratic tilt-energy gate. -/
theorem completedNativeRealHPCarrierCertificate_of_radialGammaQuadraticEnergy
    (henergy :
      CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet
        (canonicalCompletedNativeStieltjesPositivity_of_radialGammaQuadraticEnergy
          henergy hnondegenerate)) :=
  completedNativeRealHPCarrierCertificate_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialGammaQuadraticEnergy
      henergy hnondegenerate)

/-- Pointwise radial sewing remains a sufficient wrapper for the same HP
certificate. -/
theorem
    completedNativeRealHPCarrierCertificate_of_asymptoticRadialTiltBoundary
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet
        (canonicalCompletedNativeStieltjesPositivity_of_asymptoticRadialTiltBoundary
          hboundary hnondegenerate)) :=
  completedNativeRealHPCarrierCertificate_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_asymptoticRadialTiltBoundary
      hboundary hnondegenerate)

/-- Global radial sewing is retained as a convenient sufficient interface. -/
theorem completedNativeRealHPCarrierCertificate_of_radialTiltBoundary
    (hboundary : CanonicalCompletedC3RadialTiltBoundaryIntertwining)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet
        (canonicalCompletedNativeStieltjesPositivity_of_radialTiltBoundary
          hboundary hnondegenerate)) :=
  completedNativeRealHPCarrierCertificate_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialTiltBoundary
      hboundary hnondegenerate)

/-- The two geometric radial obligations instantiate the HP certificate
without a separate matrix nondegeneracy premise. -/
theorem completedNativeRealHPCarrierCertificate_of_radialGamma
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet
        (canonicalCompletedNativeStieltjesPositivity_of_radialGamma
          hboundary hstrict)) :=
  completedNativeRealHPCarrierCertificate_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialGamma
      hboundary hstrict)

/-- Direct HP certificate from the two explicit radial geometric gates. -/
theorem completedNativeRealHPCarrierCertificate_of_radialLedger
    (hnoLeak : CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet
        (canonicalCompletedNativeStieltjesPositivity_of_radialLedger
          hnoLeak hstrict)) :=
  completedNativeRealHPCarrierCertificate_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialLedger
      hnoLeak hstrict)

/-- Final completed-native confinement endpoint exposed by the local radial
tilt route. -/
theorem
    completedNativeOperator_zero_im_eq_zero_of_asymptoticRadialTiltBoundary
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_asymptoticRadialTiltBoundary
      hboundary hnondegenerate)
    hzDomain hzero

/-- Final completed-native endpoint exposed directly by the four polarized
quadratic tilt-energy limits and finite noncollapse. -/
theorem completedNativeOperator_zero_im_eq_zero_of_radialGammaQuadraticEnergy
    (henergy :
      CanonicalCompletedC3RadialGammaDslopeQuadraticEnergyFlatness)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialGammaQuadraticEnergy
      henergy hnondegenerate)
    hzDomain hzero

/-- Global radial sewing supplies the local germ used by the final endpoint. -/
theorem completedNativeOperator_zero_im_eq_zero_of_radialTiltBoundary
    (hboundary : CanonicalCompletedC3RadialTiltBoundaryIntertwining)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_asymptoticRadialTiltBoundary
    (canonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining_of_global
      hboundary)
    hnondegenerate hzDomain hzero

/-- Final endpoint phrased only through the local radial numerator identity
and the radial Gamma no-collapse estimate. -/
theorem completedNativeOperator_zero_im_eq_zero_of_radialGamma
    (hboundary :
      CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialGamma
      hboundary hstrict)
    hzDomain hzero

/-- Final confinement endpoint depending only on the explicit channel no-leak
and finite-order radial Gamma no-collapse statements. -/
theorem completedNativeOperator_zero_im_eq_zero_of_radialLedger
    (hnoLeak : CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak)
    (hstrict : CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialLedger
      hnoLeak hstrict)
    hzDomain hzero

/-- Coefficient-injectivity form of the same endpoint. -/
theorem
    completedNativeOperator_zero_im_eq_zero_of_radialTiltBoundary_of_mulVecInjective
    (hboundary : CanonicalCompletedC3RadialTiltBoundaryIntertwining)
    (hinjective : CanonicalCompletedNativeHankelPairMulVecInjective)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_radialTiltBoundary
    hboundary
    (canonicalCompletedNativeHankelPairNondegenerate_iff_mulVecInjective.mpr
      hinjective)
    hzDomain hzero

end

end CarrySelfAdjointOperator

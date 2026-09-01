import CarrySelfAdjointOperator.CompletedC3CausalChiralDefectGram
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

/-!
# Concrete obstruction to the fixed-parameter causal chiral kernel gate

The previous finite-rank audit reduced the proposed kernel compatibility to
one concrete question: can thirteen completed symplectic camera responses be
linearly independent?  This module answers yes without a Gram, positivity,
zero, or spectral premise.

For a positive real exponent `sigma`, the Dirichlet value sequence is a
multiplicative character on positive naturals.  Dedekind independence makes
distinct such characters linearly independent.  Their consecutive
differences remain independent after adjoining the constant character at
exponent zero.  Coordinate evaluation transfers this fact to the exact
completed Dirichlet-gradient states, and the global camera isometry transfers
it once more to the completed symplectic camera states.

Thirteen explicit exponents in the genuine strip therefore exceed the
twelve-dimensional positive Wronskian trace carrier.  Consequently the
fixed-parameter kernel compatibility, and hence its defect-Gram contraction,
is impossible at every point of the open upper half-plane.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## Dirichlet characters and their consecutive differences -/

/-- The real-exponent Dirichlet character on positive natural numbers. -/
def pnatRealDirichletCharacter (sigma : ℝ) : PNat →* ℂ where
  toFun n := ((((n : ℕ) : ℝ) : ℂ)) ^ (-(sigma : ℂ))
  map_one' := by simp
  map_mul' m n := by
    change (((((m * n : PNat) : ℕ) : ℝ) : ℂ) ^ (-(sigma : ℂ))) = _
    rw [PNat.mul_coe, Nat.cast_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg
      (show 0 ≤ ((m : ℕ) : ℝ) by positivity)
      (show 0 ≤ ((n : ℕ) : ℝ) by positivity) (-(sigma : ℂ))

/-- Evaluation at two separates the real-exponent Dirichlet characters. -/
theorem pnatRealDirichletCharacter_injective :
    Function.Injective pnatRealDirichletCharacter := by
  intro sigma tau h
  have htwo := DFunLike.congr_fun h (2 : PNat)
  change (2 : ℂ) ^ (-(sigma : ℂ)) =
    (2 : ℂ) ^ (-(tau : ℂ)) at htwo
  have hreal : (2 : ℝ) ^ (-sigma) = (2 : ℝ) ^ (-tau) := by
    have htwo' :
        ((2 : ℝ) : ℂ) ^ ((-sigma : ℝ) : ℂ) =
          ((2 : ℝ) : ℂ) ^ ((-tau : ℝ) : ℂ) := by
      simpa using htwo
    rw [← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2),
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)] at htwo'
    exact Complex.ofReal_injective htwo'
  have hneg :=
    (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 2)).injective hreal
  linarith

/-- Dedekind independence specialized to all real-exponent Dirichlet
characters. -/
theorem pnatRealDirichletCharacter_linearIndependent :
    LinearIndependent ℂ
      (fun sigma : ℝ => (pnatRealDirichletCharacter sigma : PNat → ℂ)) := by
  exact (linearIndependent_monoidHom PNat ℂ).comp
    pnatRealDirichletCharacter pnatRealDirichletCharacter_injective

/-- Consecutive difference of a real-exponent Dirichlet character. -/
def pnatRealDirichletGradient (sigma : ℝ) (n : ℕ) : ℂ :=
  pnatRealDirichletCharacter sigma (n + 1).succPNat -
    pnatRealDirichletCharacter sigma n.succPNat

/-- The character difference is exactly the native positive Dirichlet
gradient used by the completed C3 state. -/
theorem pnatRealDirichletGradient_eq_positiveDirichletGradient
    (sigma : ℝ) (n : ℕ) :
    pnatRealDirichletGradient sigma n =
      positiveDirichletGradient (sigma : ℂ) n := by
  simp [pnatRealDirichletGradient, pnatRealDirichletCharacter,
    positiveDirichletGradient, natDirichletTerm, dirichletTerm]
  congr 1
  ring

/-- Consecutive differences at distinct positive exponents are linearly
independent.  If a finite combination of differences vanishes, the
corresponding combination of values is constant.  Adjoining the exponent-zero
character turns this into a relation among distinct multiplicative
characters, so Dedekind independence kills every coefficient. -/
theorem pnatRealDirichletGradient_linearIndependent
    {ι : Type*} [Fintype ι]
    (sigma : ι → ℝ) (hpos : ∀ i, 0 < sigma i)
    (hinjective : Function.Injective sigma) :
    LinearIndependent ℂ (fun i => pnatRealDirichletGradient (sigma i)) := by
  classical
  let augmentedSigma : Option ι → ℝ
    | none => 0
    | some i => sigma i
  have hAugmentedInjective : Function.Injective augmentedSigma := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j =>
            simp only [augmentedSigma] at hij
            exfalso
            exact (hpos j).ne hij
    | some i =>
        cases j with
        | none =>
            simp only [augmentedSigma] at hij
            exfalso
            exact (hpos i).ne' hij
        | some j =>
            simp only [augmentedSigma] at hij
            exact congrArg some (hinjective hij)
  have hAugmented : LinearIndependent ℂ
      (fun i : Option ι =>
        (pnatRealDirichletCharacter (augmentedSigma i) : PNat → ℂ)) :=
    pnatRealDirichletCharacter_linearIndependent.comp
      augmentedSigma hAugmentedInjective
  rw [Fintype.linearIndependent_iff] at hAugmented ⊢
  intro coeff hgradient i
  let valueSum (n : ℕ) : ℂ :=
    ∑ j, coeff j * pnatRealDirichletCharacter (sigma j) n.succPNat
  have hstep (n : ℕ) : valueSum (n + 1) = valueSum n := by
    have hpoint := congrFun hgradient n
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hpoint
    simpa only [valueSum, pnatRealDirichletGradient, mul_sub,
      Finset.sum_sub_distrib, sub_eq_zero] using hpoint
  have hconstant (n : ℕ) : valueSum n = valueSum 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [hstep n, ih]
  have hvalue (n : PNat) :
      (∑ j, coeff j * pnatRealDirichletCharacter (sigma j) n) =
        ∑ j, coeff j := by
    have hn := hconstant n.natPred
    dsimp only [valueSum] at hn
    rw [PNat.succPNat_natPred] at hn
    have hzero : (0 : ℕ).succPNat = (1 : PNat) := rfl
    rw [hzero] at hn
    simp only [map_one, mul_one] at hn
    exact hn
  let augmentedCoeff : Option ι → ℂ
    | none => -(∑ j, coeff j)
    | some j => coeff j
  have hAugmentedSum :
      ∑ j, augmentedCoeff j •
          (pnatRealDirichletCharacter (augmentedSigma j) : PNat → ℂ) = 0 := by
    funext n
    rw [Fintype.sum_option]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      augmentedCoeff, augmentedSigma, smul_eq_mul]
    rw [show pnatRealDirichletCharacter 0 n = 1 by
      simp [pnatRealDirichletCharacter]]
    change (-(∑ j, coeff j)) * 1 +
      ∑ j, coeff j * pnatRealDirichletCharacter (sigma j) n = 0
    rw [hvalue n]
    ring
  exact hAugmented augmentedCoeff hAugmentedSum (some i)

/-! ## Transfer to the completed C3 Hilbert state -/

/-- Coordinate evaluation transfers character-gradient independence to the
exact completed C3 Dirichlet-gradient states in `l2`. -/
theorem canonicalCompletedC3DirichletGradientState_realExponent_linearIndependent_complex
    {ι : Type*} [Fintype ι]
    (sigma : ι → ℝ) (hpos : ∀ i, 0 < sigma i)
    (hinjective : Function.Injective sigma) :
    LinearIndependent ℂ
      (fun i => canonicalCompletedC3DirichletGradientState
        (sigma i : ℂ) (by simpa using hpos i)) := by
  rw [Fintype.linearIndependent_iff]
  intro coeff hstate i
  have hgradient :
      ∑ j, coeff j • pnatRealDirichletGradient (sigma j) = 0 := by
    funext n
    have hcoordinate := congrArg (fun x : CarryVerticalL2 => x n) hstate
    simpa only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
      Pi.smul_apply, canonicalCompletedC3DirichletGradientState_apply,
      ← pnatRealDirichletGradient_eq_positiveDirichletGradient,
      lp.coeFn_zero, Pi.zero_apply] using hcoordinate
  exact (Fintype.linearIndependent_iff.mp
    (pnatRealDirichletGradient_linearIndependent sigma hpos hinjective))
      coeff hgradient i

/-- Realification and the injective global leg-camera isometry preserve the
independence of the completed gradient states.  Projection to the second
symplectic coordinate recovers that camera leg exactly. -/
theorem completedC3SymplecticCameraState_realExponent_linearIndependent
    {ι : Type*} [Fintype ι]
    (sigma : ι → ℝ) (hpos : ∀ i, 0 < sigma i)
    (hinjective : Function.Injective sigma) :
    LinearIndependent ℝ
      (fun i => completedC3SymplecticCameraState
        (sigma i : ℂ) (by simpa using hpos i)) := by
  have hgradientComplex :=
    canonicalCompletedC3DirichletGradientState_realExponent_linearIndependent_complex
      sigma hpos hinjective
  have hgradientReal : LinearIndependent ℝ
      (fun i => canonicalCompletedC3DirichletGradientState
        (sigma i : ℂ) (by simpa using hpos i)) :=
    hgradientComplex.restrict_scalars' ℝ
  have hleg := hgradientReal.map'
    completedC3GlobalLegCameraIsometry.toLinearMap
    (LinearMap.ker_eq_bot.mpr completedC3GlobalLegCameraIsometry.injective)
  let secondCoordinate :
      RealifiedCameraComplexification →ₗ[ℝ] CameraHilbert :=
    (WithLp.sndL 2 ℝ CameraHilbert CameraHilbert).toLinearMap
  apply LinearIndependent.of_comp secondCoordinate
  simpa [Function.comp_def, secondCoordinate,
    completedC3SymplecticCameraState, completedC3LegCameraState] using hleg

/-! ## A concrete thirteen-point obstruction family -/

/-- Thirteen distinct real exponents strictly inside the genuine strip. -/
def canonicalCausalChiralObstructionExponent (i : Fin 13) : ℝ :=
  ((i.val : ℝ) + 1) / 14

theorem canonicalCausalChiralObstructionExponent_pos (i : Fin 13) :
    0 < canonicalCausalChiralObstructionExponent i := by
  simp only [canonicalCausalChiralObstructionExponent]
  positivity

theorem canonicalCausalChiralObstructionExponent_lt_one (i : Fin 13) :
    canonicalCausalChiralObstructionExponent i < 1 := by
  have hi : (i.val : ℝ) < 13 := by
    exact_mod_cast i.isLt
  simp only [canonicalCausalChiralObstructionExponent]
  linarith

theorem canonicalCausalChiralObstructionExponent_injective :
    Function.Injective canonicalCausalChiralObstructionExponent := by
  intro i j hij
  apply Fin.ext
  have hij' : (i.val : ℝ) = (j.val : ℝ) := by
    simp only [canonicalCausalChiralObstructionExponent] at hij
    linarith
  exact_mod_cast hij'

/-- Centered-height parameters whose operator parameters are the thirteen
real obstruction exponents. -/
def canonicalCausalChiralObstructionPoint (i : Fin 13) : ℂ :=
  Complex.I *
    ((((1 : ℝ) / 2) - canonicalCausalChiralObstructionExponent i : ℝ) : ℂ)

@[simp] theorem operatorHeightParameter_canonicalCausalChiralObstructionPoint
    (i : Fin 13) :
    operatorHeightParameter (canonicalCausalChiralObstructionPoint i) =
      (canonicalCausalChiralObstructionExponent i : ℂ) := by
  simp only [operatorHeightParameter, canonicalCausalChiralObstructionPoint]
  rw [← mul_assoc, Complex.I_mul_I]
  push_cast
  ring

theorem operatorHeightParameter_canonicalCausalChiralObstructionPoint_mem_strip
    (i : Fin 13) :
    operatorHeightParameter (canonicalCausalChiralObstructionPoint i) ∈
      genuineCriticalStrip := by
  rw [operatorHeightParameter_canonicalCausalChiralObstructionPoint]
  exact ⟨by simpa using canonicalCausalChiralObstructionExponent_pos i,
    by simpa using canonicalCausalChiralObstructionExponent_lt_one i⟩

/-- The explicit thirteen completed symplectic camera responses are
real-linearly independent. -/
theorem canonicalCausalChiralObstruction_symplecticCamera_linearIndependent :
    LinearIndependent ℝ
      (fun i : Fin 13 => completedC3SymplecticCameraState
        (operatorHeightParameter (canonicalCausalChiralObstructionPoint i))
        (operatorHeightParameter_canonicalCausalChiralObstructionPoint_mem_strip i).1) := by
  simpa only [operatorHeightParameter_canonicalCausalChiralObstructionPoint] using
    completedC3SymplecticCameraState_realExponent_linearIndependent
      canonicalCausalChiralObstructionExponent
      canonicalCausalChiralObstructionExponent_pos
      canonicalCausalChiralObstructionExponent_injective

/-- The fixed-parameter causal kernel compatibility is impossible throughout
the open upper half-plane. -/
theorem not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_im_pos
    (z : ℂ) (hzIm : 0 < z.im) :
    ¬ CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt z := by
  exact
    not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_fin13_symplecticCameraIndependent
      z hzIm canonicalCausalChiralObstructionPoint
      operatorHeightParameter_canonicalCausalChiralObstructionPoint_mem_strip
      canonicalCausalChiralObstruction_symplecticCamera_linearIndependent

/-- Consequently the proposed causal defect-Gram contraction is also
impossible throughout the open upper half-plane. -/
theorem not_canonicalCompletedC3CausalChiralDefectGramNonnegativeAt_of_im_pos
    (z : ℂ) (hzIm : 0 < z.im) :
    ¬ CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z := by
  intro hdefect
  exact
    not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_im_pos z hzIm
      (canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_defectGram
        hdefect)

end

end CarrySelfAdjointOperator

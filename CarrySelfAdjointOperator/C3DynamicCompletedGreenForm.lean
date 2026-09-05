import CarrySelfAdjointOperator.C3NativeTraceDynamics
import CarrySelfAdjointOperator.CovariantCameraTraceTransport
import CarrySelfAdjointOperator.CanonicalEnrichedBoundaryResidualIdentity

/-!
# The seeded C3 log dynamics in the existing complete boundary ledger

All clocks, carriers, scalar traces and Green ports are reused. The new
expressions evaluate the existing clock and boundary form, with the seed
kept at every block. No spectral operator or native moment is constructed.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary C3TraceDynamics
open CanonicalC3AllCutoffMixedSourceHilbert

noncomputable section
set_option autoImplicit false

/-- Ordinary coordinates of a complete block, in their original order. -/
def nativeC3BlockGradient (m : ℕ) (s : ℂ) : Fin 3 → ℂ :=
  ![positiveDirichletGradient s (3*m),
    positiveDirichletGradient s (3*m+1),
    positiveDirichletGradient s (3*m+2)]

/-- Evaluate the existing gradient clock, including the incoming seed. -/
def nativeC3BlockDynamicLogJet (m : ℕ) (s : ℂ) : Fin 3 → ℂ :=
  let d : ℂ := Real.log (3*m+1 : ℕ)
  let a : ℂ := Real.log (3*m+2 : ℕ)
  let b : ℂ := Real.log (3*m+3 : ℕ)
  let c : ℂ := Real.log (3*m+4 : ℕ)
  gradientClock a b c (nativeC3BlockGradient m s) +
    positiveDirichletValue s (3*m) • ![a-d,b-a,c-b]

/-- The graph of PR 51 holds at every block, with its own incoming value. -/
theorem nativeC3BlockDynamicLogJet_eq (m : ℕ) (s : ℂ) :
    nativeC3BlockDynamicLogJet m s =
      ![positiveLogDirichletGradient s (3*m),
        positiveLogDirichletGradient s (3*m+1),
        positiveLogDirichletGradient s (3*m+2)] := by
  funext i
  fin_cases i <;>
    simp [nativeC3BlockDynamicLogJet, nativeC3BlockGradient, gradientClock,
      positiveLogDirichletGradient, positiveLogDirichletValue,
      positiveDirichletGradient, positiveDirichletValue_eq_natDirichletTerm, Nat.add_assoc] <;> ring

/-- The incoming value is reconstructed from the original seed and prefix. -/
theorem nativeC3Block_seed_eq_prefix (m : ℕ) (s : ℂ) :
    positiveDirichletValue s (3*m) = positiveDirichletValue s 0 +
      ∑ n ∈ Finset.range (3*m), positiveDirichletGradient s n := by
  have h := sum_range_forwardDifference (positiveDirichletValue s) 0 (3*m)
  have h' : (∑ n ∈ Finset.range (3*m), positiveDirichletGradient s n) =
      positiveDirichletValue s (3*m) - positiveDirichletValue s 0 := by
    simpa only [Nat.zero_add, positiveDirichletGradient,
      positiveDirichletValue_eq_natDirichletTerm, Nat.add_assoc] using h
  linear_combination -h'

theorem nativeC3BlockGradient_zero (s : ℂ) :
    nativeC3BlockGradient 0 s = nativeC3GradientTriple s := rfl

/-- The new all-block evaluation specializes to the actual PR 51 graph. -/
theorem nativeC3BlockDynamicLogJet_zero (s : ℂ) :
    nativeC3BlockDynamicLogJet 0 s = nativeC3LogGradientTriple s := by
  rw [nativeC3BlockDynamicLogJet_eq]
  rfl

/-- Explicit scalar trace of the affine clock; the initial coordinate and
incoming seed have the same coefficient, without deleting either one. -/
theorem c3AffineClock_trace (a b c d f : ℂ) (g : Fin 3 → ℂ) :
    trace (gradientClock a b c g + f • ![a-d,b-a,c-b]) =
      (a-2*b+c)*(g 0+f) + (c-2*b)*g 1 + c*g 2 := by
  simp [trace, gradientClock]
  ring

/-- This scalar polynomial is the sum of the two existing oriented cells
after substitution of the affine clock. It is not a proposed Gram. -/
def c3DynamicBoundaryPolynomial {K : Type*} [CommRing K]
    (a b c d f : K) (g : Fin 3 → K) : K :=
  (a-b)*(g 0)^2 + (a-c)*g 0*g 1 + (b-a)*g 0*g 2 +
    (b-c)*(g 1)^2 + (b-c)*g 1*g 2 +
    f*((a-b)*g 0 + (a+b-c-d)*g 1 + (b-a)*g 2)

/-- All ordinary/log, incoming-boundary and within-block cross terms. -/
theorem c3AffineClock_boundary (a b c d f : ℂ) (g : Fin 3 → ℂ) :
    let j := gradientClock a b c g + f • ![a-d,b-a,c-b]
    sameSEdgeBoundaryWedge (g 0) (g 1) (j 0) (j 1) +
      sameSEdgeBoundaryWedge (g 1) (g 2) (j 1) (j 2) =
        c3DynamicBoundaryPolynomial a b c d f g := by
  simp [sameSEdgeBoundaryWedge, gradientClock, c3DynamicBoundaryPolynomial]
  ring

/-- Read the dynamically forced log channel in all retained blocks. -/
def nativeC3DynamicLogHead (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, trace (nativeC3BlockDynamicLogJet m s)

theorem nativeC3DynamicLogHead_eq (M : ℕ) (s : ℂ) :
    nativeC3DynamicLogHead M s = finiteCanonicalLogBracketChart M s := by
  unfold nativeC3DynamicLogHead finiteCanonicalLogBracketChart
  apply Finset.sum_congr rfl
  intro m _
  rw [nativeC3BlockDynamicLogJet_eq]
  simp [trace, canonicalLogBracketBlock, positiveLogDirichletGradient]
  ring

/-- The dynamic channel is exactly the log readout of the existing prefix. -/
theorem nativeC3DynamicLogHead_eq_returnVariance (M : ℕ) (s : ℂ) :
    nativeC3DynamicLogHead M s = c3ReturnVarianceHeadReadout M s
      (canonicalCompletedC3HilbertPrefixState s (3*M)).2 := by
  rw [nativeC3DynamicLogHead_eq, c3ReturnVariance_logJetHead,
    canonicalC3AllCutoffLogJetHeadReadout_prefix_eq]

/-- Exact trace reconstruction now with the log jet forced by the clock. -/
theorem nativeC3Dynamic_completedTrace (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    let s := operatorHeightParameter z
    (Complex.I * (nativeC3DynamicLogHead M s + canonicalC3LogJetCutoffTail M s),
      1 + c3ReturnVarianceHeadReadout M s
        (canonicalCompletedC3HilbertPrefixState s (3*M)).1 +
        realCpBracketCutoffTail 3 M s) =
      (canonicalCompletedC3RawHeightCompanion z,
        canonicalCompletedC3RawHeightValue z) := by
  dsimp only
  rw [nativeC3DynamicLogHead_eq_returnVariance]
  exact c3CanonicalPrefix_returnVarianceCompletedTrace M hz

/-- Literal polynomial evaluation of the complete local boundary ledger. -/
def nativeC3DynamicLocalBoundary (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    c3DynamicBoundaryPolynomial
      (Real.log (3*m+2 : ℕ) : ℂ) (Real.log (3*m+3 : ℕ) : ℂ)
      (Real.log (3*m+4 : ℕ) : ℂ) (Real.log (3*m+1 : ℕ) : ℂ)
      (positiveDirichletValue s (3*m)) (nativeC3BlockGradient m s)

theorem canonicalC3BoundaryCells_eq_dynamic (m : ℕ) {kappa : ℂ}
    (hkappa : kappa ≠ 0) (omega : ℕ → ℂ) (homega : omega m ≠ 0) (s : ℂ) :
    (canonicalEnrichedTfvdSameSBoundaryCells kappa omega m s).total =
      c3DynamicBoundaryPolynomial
        (Real.log (3*m+2 : ℕ) : ℂ) (Real.log (3*m+3 : ℕ) : ℂ)
        (Real.log (3*m+4 : ℕ) : ℂ) (Real.log (3*m+1 : ℕ) : ℂ)
        (positiveDirichletValue s (3*m)) (nativeC3BlockGradient m s) := by
  rw [canonicalEnrichedTfvdSameSBoundaryCells_eq_gradients hkappa omega m homega s]
  have h := c3AffineClock_boundary
    (Real.log (3*m+2 : ℕ)) (Real.log (3*m+3 : ℕ))
    (Real.log (3*m+4 : ℕ)) (Real.log (3*m+1 : ℕ))
    (positiveDirichletValue s (3*m)) (nativeC3BlockGradient m s)
  change sameSEdgeBoundaryWedge (nativeC3BlockGradient m s 0)
      (nativeC3BlockGradient m s 1) (nativeC3BlockDynamicLogJet m s 0)
      (nativeC3BlockDynamicLogJet m s 1) +
    sameSEdgeBoundaryWedge (nativeC3BlockGradient m s 1)
      (nativeC3BlockGradient m s 2) (nativeC3BlockDynamicLogJet m s 1)
      (nativeC3BlockDynamicLogJet m s 2) = _ at h
  rw [nativeC3BlockDynamicLogJet_eq] at h
  simpa [nativeC3BlockGradient, TfvdSameSBoundaryCells.total] using h

theorem canonicalC3PairBoundary_eq_dynamic (M : ℕ) {kappa : ℂ}
    (hkappa : kappa ≠ 0) (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteC3EnrichedTfvdPairBoundaryForm M
        (canonicalBoundaryResidualData M kappa omega s) =
      nativeC3DynamicLocalBoundary M s := by
  rw [show canonicalBoundaryResidualData M kappa omega s =
    finiteC3EnrichedTfvdPairTransport M kappa omega s
      (canonicalEnrichedTfvdValueLogJetPair kappa omega s) from rfl,
    finiteC3EnrichedTfvdPairBoundaryForm_canonical]
  unfold finiteCanonicalSeededTfvdSameSBoundaryForm
    finiteCanonicalEnrichedTfvdSameSBoundaryTrace nativeC3DynamicLocalBoundary
  exact Finset.sum_congr rfl (fun m _ =>
    canonicalC3BoundaryCells_eq_dynamic m hkappa omega (homega m) s)

/-- The four actual sums of decoded legs after enforcing the native clock.
The edge endpoints remain ordered; these are not scalar reflected legs. -/
def nativeC3DynamicSynthesisSums (M : ℕ) (s : ℂ) : Fin 4 → ℂ :=
  ![∑ m : Fin M, (nativeC3BlockGradient m s 0 + nativeC3BlockGradient m s 1),
    ∑ m : Fin M, (nativeC3BlockGradient m s 1 + nativeC3BlockGradient m s 2),
    ∑ m : Fin M, (nativeC3BlockDynamicLogJet m s 0 + nativeC3BlockDynamicLogJet m s 1),
    ∑ m : Fin M, (nativeC3BlockDynamicLogJet m s 1 + nativeC3BlockDynamicLogJet m s 2)]

theorem canonicalC3ResidualLegs_eq_dynamic (M : ℕ) {kappa : ℂ}
    (hkappa : kappa ≠ 0) (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ)
    (mr : Fin M × Fin 2) :
    let legs := canonicalBoundaryResidualLegs M kappa omega s
    ![legs.left mr, legs.right mr, legs.jetLeft mr, legs.jetRight mr] =
      ![Fin.cases (nativeC3BlockGradient mr.1 s 0)
          (fun _ => nativeC3BlockGradient mr.1 s 1) mr.2,
        Fin.cases (nativeC3BlockGradient mr.1 s 1)
          (fun _ => nativeC3BlockGradient mr.1 s 2) mr.2,
        Fin.cases (nativeC3BlockDynamicLogJet mr.1 s 0)
          (fun _ => nativeC3BlockDynamicLogJet mr.1 s 1) mr.2,
        Fin.cases (nativeC3BlockDynamicLogJet mr.1 s 1)
          (fun _ => nativeC3BlockDynamicLogJet mr.1 s 2) mr.2] := by
  rw [nativeC3BlockDynamicLogJet_eq]
  simp [canonicalBoundaryResidualLegs, canonicalBoundaryResidualPair,
    canonicalEnrichedTfvdValueLogJetPair,
    enrichedTfvdBoundaryEdgeLeft, enrichedTfvdBoundaryEdgeRight,
    enrichedTfvdBoundaryEdgeJetLeft, enrichedTfvdBoundaryEdgeJetRight,
    canonicalSeededEnrichedTfvdGenuinePort, canonicalSeededEnrichedTfvdLogJetPort,
    canonicalEnrichedAngularTfvdCoordinate, canonicalEnrichedLogJetTfvdCoordinate,
    enrichedAngularTfvdDecode_encode _ hkappa (homega mr.1), nativeC3BlockGradient]

theorem canonicalC3ResidualSums_eq_dynamic (M : ℕ) {kappa : ℂ}
    (hkappa : kappa ≠ 0) (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    let legs := canonicalBoundaryResidualLegs M kappa omega s
    ![∑ i, legs.left i, ∑ i, legs.right i, ∑ i, legs.jetLeft i, ∑ i, legs.jetRight i] =
      nativeC3DynamicSynthesisSums M s := by
  dsimp only
  have h := canonicalC3ResidualLegs_eq_dynamic M hkappa omega homega s
  have h0 := fun mr => congrFun (h mr) 0
  have h1 := fun mr => congrFun (h mr) 1
  have h2 := fun mr => congrFun (h mr) 2
  have h3 := fun mr => congrFun (h mr) 3
  simp only [Matrix.cons_val] at h0 h1 h2 h3
  simp_rw [h0, h1, h2, h3]
  simp [nativeC3DynamicSynthesisSums, Fintype.sum_prod_type, Fin.cases]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- First residual channel: the oriented dynamic polynomial minus the
existing reflected Green port. No radial or dormant term is dropped. -/
theorem canonicalC3GreenProvenance_eq_dynamic (M : ℕ) {kappa : ℂ}
    (hkappa : kappa ≠ 0) (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s =
      nativeC3DynamicLocalBoundary M s -
        greenForm (𝕜 := ℂ) (finiteC3GenuineBracketGreenBoundaryPair (3*M) s)
          (finiteC3GenuineBracketGreenBoundaryPair (3*M) (reflectedParameter s)) := by
  have h := finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
    M hkappa omega homega s
  change finiteC3EnrichedTfvdPairBoundaryForm M
    (canonicalBoundaryResidualData M kappa omega s) - _ = _ at h
  rw [canonicalC3PairBoundary_eq_dynamic M hkappa omega homega s] at h
  linear_combination -h

/-- Second channel: all ordered cross edges, evaluated with the forced log jet. -/
theorem canonicalC3CrossProvenance_eq_dynamic (M : ℕ) {kappa : ℂ}
    (hkappa : kappa ≠ 0) (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    let S := nativeC3DynamicSynthesisSums M s
    canonicalBoundaryCrossProvenance M kappa omega s =
      S 1*S 2 - S 0*S 3 - nativeC3DynamicLocalBoundary M s := by
  dsimp only
  let legs := canonicalBoundaryResidualLegs M kappa omega s
  have hs := canonicalC3ResidualSums_eq_dynamic M hkappa omega homega s
  have h0 := congrFun hs 0
  have h1 := congrFun hs 1
  have h2 := congrFun hs 2
  have h3 := congrFun hs 3
  simp only [Matrix.cons_val] at h0 h1 h2 h3
  have hl := sum_enrichedTfvdBoundaryEdges_eq_pairBoundaryForm M kappa omega s
    (canonicalBoundaryResidualPair kappa omega s)
  change (∑ i, sameSEdgeBoundaryWedge (legs.left i) (legs.right i)
      (legs.jetLeft i) (legs.jetRight i)) =
    finiteC3EnrichedTfvdPairBoundaryForm M (canonicalBoundaryResidualData M kappa omega s) at hl
  rw [canonicalC3PairBoundary_eq_dynamic M hkappa omega homega s] at hl
  change twoLegBoundaryCrossProvenance legs.left legs.right legs.jetLeft legs.jetRight = _
  unfold twoLegBoundaryCrossProvenance
  rw [← sameSEdgeBoundaryWedge_sum_eq_pairwiseLedger, hl]
  change (∑ i, legs.right i)*(∑ i, legs.jetLeft i) -
    (∑ i, legs.left i)*(∑ i, legs.jetRight i) - _ = _
  rw [h0, h1, h2, h3]

/-- Third channel: the four-leg synthesis correction with the actual
seeded value and dynamic log readout. -/
theorem canonicalC3ReadoutCorrection_eq_dynamic (M : ℕ) {kappa : ℂ}
    (hkappa : kappa ≠ 0) (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    let S := nativeC3DynamicSynthesisSums M s
    canonicalBoundaryReadoutResidualCorrection M kappa omega s =
      conj (finiteBracketedDirichletChart 3 M s)*nativeC3DynamicLogHead M s -
        conj (nativeC3DynamicLogHead M s)*finiteBracketedDirichletChart 3 M s -
        (S 1*S 2-S 0*S 3) := by
  dsimp only
  have h := scalarBoundaryWedge_eq_summedTwoLeg_add_residualCorrection
    (canonicalBoundaryResidualData M kappa omega s).valueReadout
    (canonicalBoundaryResidualData M kappa omega s).logJetReadout
    (canonicalBoundaryResidualLegs M kappa omega s)
  have ht := finiteC3EnrichedTfvdPairTransport_canonical M hkappa omega homega s
  change (canonicalBoundaryResidualData M kappa omega s).valueReadout = _ ∧
    (canonicalBoundaryResidualData M kappa omega s).logJetReadout = _ ∧ _ at ht
  rw [ht.1, ht.2.1, ← nativeC3DynamicLogHead_eq] at h
  have hs := canonicalC3ResidualSums_eq_dynamic M hkappa omega homega s
  have h0 := congrFun hs 0
  have h1 := congrFun hs 1
  have h2 := congrFun hs 2
  have h3 := congrFun hs 3
  simp only [Matrix.cons_val] at h0 h1 h2 h3
  rw [h0, h1, h2, h3] at h
  unfold canonicalBoundaryReadoutResidualCorrection
  dsimp only
  rw [ht.1, ht.2.1, ← nativeC3DynamicLogHead_eq]
  unfold scalarBoundaryWedge sameSEdgeBoundaryWedge at h
  linear_combination -h

/-- The two local synthesis terms cancel between residual channels, but
the explicit scalar/reflected-Green difference remains. -/
theorem canonicalC3ThreeResiduals_eq_dynamic (M : ℕ) {kappa : ℂ}
    (hkappa : kappa ≠ 0) (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s +
      canonicalBoundaryCrossProvenance M kappa omega s +
      canonicalBoundaryReadoutResidualCorrection M kappa omega s =
      conj (finiteBracketedDirichletChart 3 M s)*nativeC3DynamicLogHead M s -
        conj (nativeC3DynamicLogHead M s)*finiteBracketedDirichletChart 3 M s -
        greenForm (𝕜 := ℂ) (finiteC3GenuineBracketGreenBoundaryPair (3*M) s)
          (finiteC3GenuineBracketGreenBoundaryPair (3*M) (reflectedParameter s)) := by
  rw [canonicalC3GreenProvenance_eq_dynamic M hkappa omega homega s,
    canonicalC3CrossProvenance_eq_dynamic M hkappa omega homega s,
    canonicalC3ReadoutCorrection_eq_dynamic M hkappa omega homega s]
  ring

/-- A native block has a strictly negative logarithmic second difference.
Thus its initial coordinate remains dynamically visible at every depth. -/
theorem nativeC3Block_logTraceGap_neg (m : ℕ) :
    Real.log (3*m+2 : ℕ) - 2*Real.log (3*m+3 : ℕ) +
      Real.log (3*m+4 : ℕ) < 0 := by
  have hp : (0 : ℝ) < (3*m+2 : ℕ) := by positivity
  have hq : (0 : ℝ) < (3*m+3 : ℕ) := by positivity
  have hr : (0 : ℝ) < (3*m+4 : ℕ) := by positivity
  have hlt : ((3*m+2 : ℕ) : ℝ)*((3*m+4 : ℕ) : ℝ) <
      ((3*m+3 : ℕ) : ℝ)*((3*m+3 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have h := Real.log_lt_log (mul_pos hp hr) hlt
  rw [Real.log_mul (ne_of_gt hp) (ne_of_gt hr),
    Real.log_mul (ne_of_gt hq) (ne_of_gt hq)] at h
  linarith

/-- Exact sign witnesses for the local oriented form on the consistent
zero-seed graph. These are finite test states, not canonical parameter values. -/
theorem c3DynamicBoundaryPolynomial_sign_witnesses (m : ℕ) :
    c3DynamicBoundaryPolynomial
        (Real.log (3*m+2 : ℕ)) (Real.log (3*m+3 : ℕ))
        (Real.log (3*m+4 : ℕ)) (Real.log (3*m+1 : ℕ)) 0 ![1,0,0] < 0 ∧
      0 < c3DynamicBoundaryPolynomial
        (Real.log (3*m+2 : ℕ)) (Real.log (3*m+3 : ℕ))
        (Real.log (3*m+4 : ℕ)) (Real.log (3*m+1 : ℕ)) 0 ![1,0,2] := by
  have h : Real.log (3*m+2 : ℕ) < Real.log (3*m+3 : ℕ) :=
    Real.log_lt_log (by positivity) (by exact_mod_cast (show 3*m+2 < 3*m+3 by omega))
  simp only [c3DynamicBoundaryPolynomial, Matrix.cons_val, mul_zero, mul_one,
    zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow, add_zero]
  constructor <;> linarith

/-- Real part of the scalar skew boundary vanishes independently of any
dynamic hypothesis. This keeps the orientation of the original ledger. -/
theorem scalarBoundaryWedge_real_part_zero (V J : ℂ) :
    (scalarBoundaryWedge V J).re = 0 := by
  simp [scalarBoundaryWedge, Complex.mul_re]
  ring

/-- On the canonical one-block curve, the dynamically evaluated residuals
still have a nonzero real part off the critical line. No free log pulse is used. -/
theorem canonicalC3Dynamic_threeResiduals_ne_zero {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) (hoff : s.re ≠ (1:ℝ)/2) :
    finiteCanonicalTfvdSameSGreenProvenanceDefect 3 1 s +
      canonicalBoundaryCrossProvenance 1 1 (fun _ => 1) s +
      canonicalBoundaryReadoutResidualCorrection 1 1 (fun _ => 1) s ≠ 0 := by
  rw [canonicalC3ThreeResiduals_eq_dynamic 1 (by norm_num : (1:ℂ) ≠ 0)
    (fun _ => 1) (by intro m; norm_num) s]
  have hg := canonicalEnrichedC3ReflectedGreenBulk_re_eq_zero_iff_re_eq_half hs
  have heq : canonicalEnrichedC3ReflectedGreenBulk s =
      greenForm (𝕜 := ℂ) (finiteC3GenuineBracketGreenBoundaryPair (3*1) s)
        (finiteC3GenuineBracketGreenBoundaryPair (3*1) (reflectedParameter s)) := by
    unfold canonicalEnrichedC3ReflectedGreenBulk
    rw [canonicalEnrichedC3SourcePort_eq_greenBoundaryPair,
      canonicalEnrichedC3SourcePort_eq_greenBoundaryPair]
  rw [← heq]
  change scalarBoundaryWedge (finiteBracketedDirichletChart 3 1 s)
      (nativeC3DynamicLogHead 1 s) - canonicalEnrichedC3ReflectedGreenBulk s ≠ 0
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.zero_re, scalarBoundaryWedge_real_part_zero,
    zero_sub, neg_eq_zero] at hr
  exact hoff (hg.mp hr)

/-- Completion of the unrotated scalar boundary retains all four cross
terms and the tail-tail boundary. -/
theorem scalarBoundaryWedge_add_tails (V J v j : ℂ) :
    scalarBoundaryWedge (V+v) (J+j) = scalarBoundaryWedge V J +
      (conj V*j + conj v*J - conj J*v - conj j*V) + scalarBoundaryWedge v j := by
  simp only [scalarBoundaryWedge, map_add]
  ring

/-- The actual Green form of the rotated trace uses a sum, not the scalar
skew difference. Both parameters and every head/tail product are retained. -/
theorem c3RotatedTrace_greenForm_with_tails (V J W K v j w k : ℂ) :
    greenForm (𝕜 := ℂ) (Complex.I*(J+j), V+v) (Complex.I*(K+k), W+w) =
      Complex.I * (conj V*K + conj J*W +
        (conj V*k + conj v*K + conj J*w + conj j*W) +
        (conj v*k + conj j*w)) := by
  simp [greenForm, map_add, map_mul]
  ring

/-- Apply the computed Green form to the canonical dynamically constrained
trace at two independent native parameters and arbitrary cutoffs. -/
theorem nativeC3Dynamic_completedTrace_greenForm (M N : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    let s := operatorHeightParameter z
    let t := operatorHeightParameter w
    let V := finiteBracketedDirichletChart 3 M s
    let W := finiteBracketedDirichletChart 3 N t
    let J := nativeC3DynamicLogHead M s
    let K := nativeC3DynamicLogHead N t
    let v := realCpBracketCutoffTail 3 M s
    let q := realCpBracketCutoffTail 3 N t
    let j := canonicalC3LogJetCutoffTail M s
    let k := canonicalC3LogJetCutoffTail N t
    greenForm (𝕜 := ℂ)
      (canonicalCompletedC3RawHeightCompanion z, canonicalCompletedC3RawHeightValue z)
      (canonicalCompletedC3RawHeightCompanion w, canonicalCompletedC3RawHeightValue w) =
      Complex.I * (conj V*K + conj J*W +
        (conj V*k + conj v*K + conj J*q + conj j*W) +
        (conj v*k + conj j*q)) := by
  dsimp only
  rw [← nativeC3Dynamic_completedTrace M hz, ← nativeC3Dynamic_completedTrace N hw]
  rw [c3ReturnVariance_valueHead, c3ReturnVariance_valueHead,
    canonicalC3AllCutoffValueHeadReadout_prefix_eq,
    canonicalC3AllCutoffValueHeadReadout_prefix_eq]
  exact c3RotatedTrace_greenForm_with_tails _ _ _ _ _ _ _ _

/-- Concrete native parameter witness, using the actual finite canonical
family rather than an independent variation of its log channel. -/
theorem canonicalC3Dynamic_threeResiduals_quarter_ne_zero :
    finiteCanonicalTfvdSameSGreenProvenanceDefect 3 1 (1/4) +
      canonicalBoundaryCrossProvenance 1 1 (fun _ => 1) (1/4) +
      canonicalBoundaryReadoutResidualCorrection 1 1 (fun _ => 1) (1/4) ≠ 0 := by
  apply canonicalC3Dynamic_threeResiduals_ne_zero
  · norm_num [genuineCriticalStrip]
  · norm_num

/-- Insert the exact two tails into the already proved three-channel
identity. The boundary shift includes all cross terms and the tail wedge. -/
theorem nativeC3Dynamic_completedScalarBoundary_ledger (M : ℕ) (s : ℂ) :
    let V := finiteBracketedDirichletChart 3 M s
    let J := nativeC3DynamicLogHead M s
    let v := realCpBracketCutoffTail 3 M s
    let j := canonicalC3LogJetCutoffTail M s
    scalarBoundaryWedge (V+v) (J+j) =
      greenForm (𝕜 := ℂ) (finiteC3GenuineBracketGreenBoundaryPair (3*M) s)
        (finiteC3GenuineBracketGreenBoundaryPair (3*M) (reflectedParameter s)) +
      (finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s +
        canonicalBoundaryCrossProvenance M 1 (fun _ => 1) s +
        canonicalBoundaryReadoutResidualCorrection M 1 (fun _ => 1) s) +
      (conj V*j + conj v*J - conj J*v - conj j*V) + scalarBoundaryWedge v j := by
  dsimp only
  rw [scalarBoundaryWedge_add_tails]
  have h := canonicalEnrichedScalarBoundary_eq_green_add_explicitDefects
    M (by norm_num : (1:ℂ) ≠ 0) (fun _ => 1) (by intro m; norm_num) s
  have ht := finiteC3EnrichedTfvdPairTransport_canonical
    M (by norm_num : (1:ℂ) ≠ 0) (fun _ => 1) (by intro m; norm_num) s
  change (canonicalBoundaryResidualData M 1 (fun _ => 1) s).valueReadout = _ ∧
    (canonicalBoundaryResidualData M 1 (fun _ => 1) s).logJetReadout = _ ∧ _ at ht
  rw [ht.1, ht.2.1, ← nativeC3DynamicLogHead_eq] at h
  rw [h]

/-- Restoring all three residues gives literal outer minus inner endpoints
in both the value and the dynamically constrained log channel. -/
theorem nativeC3Dynamic_threeResidue_totals (M : ℕ) (s : ℂ) :
    (∑ m : Fin M, (nativeC3BlockGradient m s 0 + nativeC3BlockGradient m s 1 +
      nativeC3BlockGradient m s 2)) =
        positiveDirichletValue s (3*M) - positiveDirichletValue s 0 ∧
    (∑ m : Fin M, (nativeC3BlockDynamicLogJet m s 0 +
      nativeC3BlockDynamicLogJet m s 1 + nativeC3BlockDynamicLogJet m s 2)) =
        (Real.log (3*M+1 : ℕ) : ℂ)*positiveDirichletValue s (3*M) := by
  constructor
  · simp only [nativeC3BlockGradient, Matrix.cons_val, Finset.sum_fin_eq_sum_range]
    have hc : (∑ x ∈ Finset.range M, if h : x < M then
        positiveDirichletGradient s (3*x) + positiveDirichletGradient s (3*x+1) +
          positiveDirichletGradient s (3*x+2) else 0) =
        ∑ x ∈ Finset.range M, (positiveDirichletGradient s (3*x) +
          positiveDirichletGradient s (3*x+1) + positiveDirichletGradient s (3*x+2)) :=
      Finset.sum_congr rfl (fun x hx => dif_pos (Finset.mem_range.mp hx))
    rw [hc, sum_range_threeBlocks_eq_range]
    have h := nativeC3Block_seed_eq_prefix M s
    linear_combination -h
  · simp_rw [nativeC3BlockDynamicLogJet_eq]
    simp only [Matrix.cons_val, Finset.sum_fin_eq_sum_range]
    have hc : (∑ x ∈ Finset.range M, if h : x < M then
        positiveLogDirichletGradient s (3*x) + positiveLogDirichletGradient s (3*x+1) +
          positiveLogDirichletGradient s (3*x+2) else 0) =
        ∑ x ∈ Finset.range M, (positiveLogDirichletGradient s (3*x) +
          positiveLogDirichletGradient s (3*x+1) + positiveLogDirichletGradient s (3*x+2)) :=
      Finset.sum_congr rfl (fun x hx => dif_pos (Finset.mem_range.mp hx))
    rw [hc, sum_range_threeBlocks_eq_range]
    have h := sum_range_forwardDifference (positiveLogDirichletValue s) 0 (3*M)
    simpa [positiveLogDirichletGradient, positiveLogDirichletValue] using h

/-- The four edge sums are endpoint data minus the residue that each
readout omits. Thus their synthesis does not become a pure endpoint. -/
theorem nativeC3Dynamic_sums_add_omittedResidues (M : ℕ) (s : ℂ) :
    let S := nativeC3DynamicSynthesisSums M s
    let E := positiveDirichletValue s (3*M) - positiveDirichletValue s 0
    let L := (Real.log (3*M+1 : ℕ) : ℂ)*positiveDirichletValue s (3*M)
    S 0 + (∑ m : Fin M, nativeC3BlockGradient m s 2) = E ∧
    S 1 + (∑ m : Fin M, nativeC3BlockGradient m s 0) = E ∧
    S 2 + (∑ m : Fin M, nativeC3BlockDynamicLogJet m s 2) = L ∧
    S 3 + (∑ m : Fin M, nativeC3BlockDynamicLogJet m s 0) = L := by
  dsimp only
  have h := nativeC3Dynamic_threeResidue_totals M s
  simp only [nativeC3DynamicSynthesisSums, Matrix.cons_val]
  simp_rw [← Finset.sum_add_distrib]
  refine ⟨h.1, ?_, h.2, ?_⟩
  · convert h.1 using 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  · convert h.2 using 1
    apply Finset.sum_congr rfl
    intro m _
    ring

end
end CarrySelfAdjointOperator

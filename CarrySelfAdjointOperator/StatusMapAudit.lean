import CarrySelfAdjointOperator.NativeScalarZetaIdentification
import CarrySelfAdjointOperator.CompletedNativePositionalBranchBarrier
import CarrySelfAdjointOperator.NativeBracketTfvdGreenSameGeometry
import CarrySelfAdjointOperator.LinearPMapPointSpectrum
import CarrySelfAdjointOperator.CompletedNativeGeometricLowOrderClosure
import CarrySelfAdjointOperator.CompletedNativeXiCosineMomentHerglotzGate
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy
import CarrySelfAdjointOperator.CompletedNativePoleAtomHankelPerturbation
import CarrySelfAdjointOperator.GreenJetMaximalAdjointSquare
import CarrySelfAdjointOperator.GreenJetReciprocalSignedHeightOperator
import CarrySelfAdjointOperator.CompletedNativeGreenWeylHeight
import CarrySelfAdjointOperator.ConditionalCriticalLineConfinement

/-!
# Status map audit

A single verifiable ledger of the load-bearing anchors, layer by layer, with a
two-axis reading protocol:

* **Axiom axis** — every anchor below is printed with `#print axioms`.  A clean
  `[propext, Classical.choice, Quot.sound]` certifies two things at once: the
  proof uses no `sorry`/`admit` (no `sorryAx`) and it introduces no
  project-specific axiom.  Only the three standard Mathlib foundations appear.

* **Hypothesis axis** — recorded in the comment above each anchor.  This is the
  distinction the axiom line cannot see (a conditional theorem still has clean
  axioms):
    - `UNCONDITIONAL` — the statement assumes only domain membership / typeclass
      structure.  No positivity, no zero-set, no Green, no Wronskian input.
    - `GRAM-GATED` — the statement assumes exactly one nontrivial input, the
      moment-kernel Gram representation
      `IsGreenWronskianMomentKernelGramRepresentation` (equivalently the bundled
      `HasCanonicalCompletedNativeGreenMomentJets`).  This is the single
      remaining positivity obligation of the whole construction.
    - `GREEN-GATED` — the RH-reduction capstone, which consumes the Green
      off-axis diagonal state hypothesis.

The map is complete in the following sense: Layers 1–4 are `UNCONDITIONAL`; the
entire self-adjoint operator apparatus (Layer 5) is a *theorem* whose only
nontrivial premise is the Gram representation; Layer 6 is the conditional
critical-line conclusion.  Nothing between the geometry and the operator is left
implicit.
-/

namespace CarrySelfAdjointOperator.StatusMapAudit

/- ======================================================================== -/
/- LAYER 1 — Zeta-free geometric genesis.                    UNCONDITIONAL. -/
/- ======================================================================== -/

/- Carry-native scalar is literally Mathlib's `riemannZeta` on the open strip.
   Only hypothesis: `s ∈ genuineCriticalStrip` (domain membership).  The path to
   ζ never uses the functional equation, the Euler product, or any zero. -/
#print axioms nativeScalar_eq_riemannZeta

/- The σ = 1/2 mass law as a pure geometric consequence: unit branch mass holds
   exactly at the centered exponent, for every base `b > 1`.  Only hypotheses:
   `1 < b`, `0 < sigma`.  No primality, zero-set, Green, Wronskian, or spectral
   hypothesis is used.  (This is the "consequence, not the confinement
   mechanism" fact.) -/
#print axioms branchNormSq_allBase_barrier

/- ======================================================================== -/
/- LAYER 2 — Exact head–tail identity.                       UNCONDITIONAL. -/
/- ======================================================================== -/

/- `finiteBracket(cutoff) + centerTail(cutoff) = cpChartFactor · genuineζ`, an
   EXACT discrete identity for every cutoff (not an asymptotic).  Only
   hypothesis: `s ∈ nativeScalarDomain`.  The camera and cutoff cancel. -/
#print axioms completeNativeC3HeadTail_eq_cpFactor_mul_genuineContinuation

/- ======================================================================== -/
/- LAYER 3 — Real ↔ complex spectral bridge.                 UNCONDITIONAL. -/
/- ======================================================================== -/

/- Complexification neither creates nor loses real point spectrum: a real
   eigenvalue of the complexification yields a real eigenvector of the original
   real operator.  Pure functional analysis; no positivity. -/
#print axioms LinearPMap.hasRealEigenvalue_of_complexification_hasEigenvalue

/- ======================================================================== -/
/- LAYER 4 — Low-order / first-section closure.       UNCONDITIONAL (theta). -/
/- ======================================================================== -/

/- First moment strictly positive, `0 < h₀`, with no hypothesis (discharged via
   the Riemann-theta xi-cosine low-moment certificate). -/
#print axioms canonicalCompletedNativeLogDerivativeMoment_zero_pos

/- Unconditional low-order Herglotz curvature: `0 < h₀` and `0 < h₁`, and the
   two-point radial sample is eventually PSD.  No hypothesis. -/
#print axioms canonicalCompletedNativeLowOrderHerglotzCurvaturePositive

/- The 1×1 Hankel section is positive definite, unconditionally. -/
#print axioms canonicalCompletedNativeHankelGram_one_posDef

/- Unconditional transversality of the central symplectic crossing: the signed
   chiral balance variation is nonzero (first variation tilts the two equal
   chiral energies by exactly `D(0)·h₀`, `h₀ > 0`).  No hypothesis. -/
#print axioms canonicalCompletedC3FullWronskianCentralChiralBalanceVariation_ne_zero

/- Pole-atom rank-one perturbation, structural Loewner comparisons between the
   canonical and completed-raw Hankel towers.  No hypothesis. -/
#print axioms hankelGram_canonical_le_completedRaw
#print axioms shiftedHankel_completedRaw_le_canonical

/- ======================================================================== -/
/- LAYER 5 — Self-adjoint height operator.   GRAM-GATED (one hypothesis).   -/
/-                                                                          -/
/- Each theorem below is a genuine self-adjointness statement `H* = H`.     -/
/- Its ONLY nontrivial premise is the moment-kernel Gram representation     -/
/- (`IsGreenWronskianMomentKernelGramRepresentation` / the bundled          -/
/- `HasCanonicalCompletedNativeGreenMomentJets`).  Positivity of the Jacobi -/
/- form is the squared norm of the Green energy factor, `J = B*B`, so       -/
/- self-adjointness follows *automatically once the Gram input is supplied*.-/
/- ======================================================================== -/

/- Maximal real self-adjoint energy square `J = B*B` (even sector). -/
#print axioms closedGreenJetEnergyAdjointSquare_isMaximalRealSelfAdjoint

/- Maximal real self-adjoint reciprocal signed-height operator (the height
   operator whose eigenvalues are the heights). -/
#print axioms closedGreenJetReciprocalSignedHeightOperator_isMaximalRealSelfAdjoint

/- Concrete completed-native height operator: `H.adjoint = H`, from the concrete
   Green moment-jet certificate (`greenMomentJets`) plus global parity
   independence.  The `greenMomentJets` premise *is* the Gram gate. -/
#print axioms canonicalCompletedNativeHeightOperator_adjoint_eq_of_greenMomentJets

/- ======================================================================== -/
/- LAYER 6 — Conditional critical-line confinement.          GREEN-GATED.   -/
/-                                                                          -/
/- The RH-shaped conclusion `Re s = 1/2`, conditional on the canonical      -/
/- completed-native Green off-axis diagonal state hypothesis.  This is the  -/
/- honest terminal reduction: geometry + operator ⟹ (given the Green gate)  -/
/- every zeta zero in the strip sits on the critical line.                  -/
/- ======================================================================== -/

#print axioms riemannZeta_zero_re_eq_half_of_canonicalGreenState

end CarrySelfAdjointOperator.StatusMapAudit

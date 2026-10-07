import CarrySelfAdjointOperator.CompletedNativeRegularizedGammaLeakSewing
import CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridgeAudit
import CarrySelfAdjointOperator.CompletedNativeAmbientRadialIntertwiningNoGo

/-! Source-first roots: diagnostics below are kept outside this closure. -/
set_option maxHeartbeats 0
namespace CarrySelfAdjointOperator
#assert_prime_depth_source_axioms canonicalCompletedC3NormalizedGammaPortResponse
#print axioms canonicalCompletedC3NormalizedGammaPortResponse
#assert_prime_depth_source_axioms canonicalCompletedC3NormalizedResolvedLeakResponse
#print axioms canonicalCompletedC3NormalizedResolvedLeakResponse
#assert_prime_depth_source_axioms canonicalCompletedC3NormalizedAmbientResponse_eq_gammaPort_add_resolvedLeak
#print axioms canonicalCompletedC3NormalizedAmbientResponse_eq_gammaPort_add_resolvedLeak
#assert_prime_depth_source_axioms canonicalCompletedC3NormalizedGammaLeakPairing
#print axioms canonicalCompletedC3NormalizedGammaLeakPairing
#assert_prime_depth_source_axioms canonicalCompletedC3NormalizedAmbientKernel_eq_gammaLeakPairing
#print axioms canonicalCompletedC3NormalizedAmbientKernel_eq_gammaLeakPairing
#assert_prime_depth_source_axioms canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_materialCompletion
#print axioms canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_materialCompletion
#assert_prime_depth_source_axioms canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_dslope
#print axioms canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_dslope
#assert_prime_depth_source_axioms canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope
#print axioms canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope
#assert_prime_depth_source_axioms canonicalCompletedC3Dslope_eq_materialCompletion_div
#print axioms canonicalCompletedC3Dslope_eq_materialCompletion_div
#assert_prime_depth_source_axioms canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_materialCompletion
#print axioms canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_materialCompletion
#assert_prime_depth_source_axioms canonicalCompletedC3RegularizedLedger_eventually_eq_gammaLeak_sub_materialCompletion
#print axioms canonicalCompletedC3RegularizedLedger_eventually_eq_gammaLeak_sub_materialCompletion
#assert_oriented_green_source
  canonicalCompletedC3NormalizedGammaPortResponse
  canonicalCompletedC3NormalizedResolvedLeakResponse
  canonicalCompletedC3NormalizedAmbientResponse_eq_gammaPort_add_resolvedLeak
  canonicalCompletedC3NormalizedGammaLeakPairing
  canonicalCompletedC3NormalizedAmbientKernel_eq_gammaLeakPairing
  canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_materialCompletion
  canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_dslope
  canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope
  canonicalCompletedC3Dslope_eq_materialCompletion_div
  canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_materialCompletion
  canonicalCompletedC3RegularizedLedger_eventually_eq_gammaLeak_sub_materialCompletion

/-! Finite entry canaries use the existing ambient grid. -/
open scoped ComplexConjugate
noncomputable section

example (k : ℕ) :
    let z := canonicalCompletedC3AmbientRadialTiltPoint k 2 (0 : Fin 2)
    let w := canonicalCompletedC3AmbientRadialTiltPoint k 2 (0 : Fin 2)
    canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k 2 0 0 =
      canonicalCompletedC3NormalizedGammaLeakPairing z w
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k 2 0)
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k 2 0)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 2 0)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 2 0) -
      canonicalCompletedNativePolarizedDslopeKernel z w :=
  canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope k 2 0 0

example (k : ℕ) :
    let z := canonicalCompletedC3AmbientRadialTiltPoint k 2 (0 : Fin 2)
    let w := canonicalCompletedC3AmbientRadialTiltPoint k 2 (1 : Fin 2)
    canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k 2 0 1 =
      canonicalCompletedC3NormalizedGammaLeakPairing z w
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k 2 0)
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k 2 1)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 2 0)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 2 1) -
      canonicalCompletedNativePolarizedDslopeKernel z w :=
  canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope k 2 0 1

example (k : ℕ) :
    let z := canonicalCompletedC3AmbientRadialTiltPoint k 2 (1 : Fin 2)
    let w := canonicalCompletedC3AmbientRadialTiltPoint k 2 (1 : Fin 2)
    canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k 2 1 1 =
      canonicalCompletedC3NormalizedGammaLeakPairing z w
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k 2 1)
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k 2 1)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 2 1)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 2 1) -
      canonicalCompletedNativePolarizedDslopeKernel z w :=
  canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope k 2 1 1

/-! Independent diagnostic only: the pre-existing moment comparison/no-go
is not used to define or prove any source-first root above. Rewriting the
four-pairing difference preserves the old strictly positive central excess. -/
example (N : ℕ) (i j : Fin N) :
    Filter.Tendsto (fun k =>
      let z := canonicalCompletedC3AmbientRadialTiltPoint k N i
      let w := canonicalCompletedC3AmbientRadialTiltPoint k N j
      canonicalCompletedC3NormalizedGammaLeakPairing z w
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N j)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j) -
      canonicalCompletedNativePolarizedDslopeKernel z w)
      Filter.atTop (nhds (canonicalCompletedC3NormalizedAmbientCentralExcess : ℂ)) := by
  exact (canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto_centralExcess
    N i j).congr' (Filter.Eventually.of_forall fun k =>
      canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope k N i j)

example : 0 < canonicalCompletedC3NormalizedAmbientCentralExcess :=
  canonicalCompletedC3NormalizedAmbientCentralExcess_pos
end
end CarrySelfAdjointOperator

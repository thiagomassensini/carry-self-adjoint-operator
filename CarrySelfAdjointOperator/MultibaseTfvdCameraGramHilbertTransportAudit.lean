import CarrySelfAdjointOperator.MultibaseTfvdCameraGramHilbertTransport

namespace CarrySelfAdjointOperator

/-!
Trust audit for the finite Hilbert-valued camera Gram transport.

The declarations audited here only lift finite real matrices over the outer
camera/state indices.  They do not identify a camera label with a vertical
coordinate, and they do not add an outer Hilbert structure to the global
finitely-supported camera carrier.
-/

#print axioms finiteHilbertMatrixSynthesis_comp
#print axioms finiteHilbertMatrixSynthesis_inner_gram
#print axioms finiteCameraHilbertRawSynthesis_inner
#print axioms finiteCameraHilbertRawSynthesis_single_channel
#print axioms finiteCanonicalCameraHilbertSynthesis_isometry
#print axioms finiteCanonicalCameraHilbertReadout_synthesis
#print axioms finiteCanonicalEnrichedCameraHilbert_parseval
#print axioms finiteLiteralCameraHilbertRawSynthesis_inner
#print axioms finiteLiteralWhitenedCameraResolvedLogSlopePrefixState_isometry
#print axioms finiteHilbertMatrixSynthesis_map_linearMap_commutes

end CarrySelfAdjointOperator

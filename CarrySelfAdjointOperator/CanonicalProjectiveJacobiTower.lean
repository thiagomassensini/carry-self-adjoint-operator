import CarrySelfAdjointOperator.CanonicalLDLPrefixReduction

/-!
# Canonical projective Jacobi tower compatibility import

The canonical LDL prefix reduction now contains the projective Jacobi
interface together with its unconditional prefix-compatibility proof.
Re-export that implementation so existing imports retain the same declaration
names and statements, while importing both modules uses one definition of
each tower object and theorem.
-/

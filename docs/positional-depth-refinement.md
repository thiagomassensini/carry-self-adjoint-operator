# Refinamento posicional entre profundidades

O módulo `PositionalDepthRefinement.lean` usa diretamente a fundação do
`CarryGeometry`, sem criar um índice artificial `positionalDepth`.

Para o mesmo `n`, a carta na profundidade `k` é

\[
(q_k,r_k)=\bigl(\texttt{quotientAtDepth}(b,k,n),
\texttt{residueAtDepth}(b,k,n)\bigr).
\]

A carta na profundidade seguinte satisfaz exatamente

\[
q_{k+1}=q_k/b,
\qquad
r_{k+1}=r_k+b^k(q_k\bmod b).
\]

Em Lean, isso é expresso por
`quotientAtDepth_succ_eq_refinedQuotient` e
`residueAtDepth_succ_eq_refinedResidue`. O par completo é transportado por
`positionalDepthCoordinates_succ_eq_refinement` e continua reconstruindo o
mesmo `n` em `positionalDepthRefinement_reconstructs`.

A prova usa apenas `Nat.mod_pow_succ`, `Nat.div_div_eq_div_mul` e a
reconstrução existente `positionalDecompositionAtDepth`. Assim, aumentar a
profundidade é uma mudança de carta do mesmo valor aritmético:

\[
n=r_k+b^kq_k=r_{k+1}+b^{k+1}q_{k+1}.
\]

Esta etapa ainda não identifica esse transporte de coordenadas com
`finiteDepthShift`. Os domínios são diferentes: a carta posicional é um par
de naturais dependente de `(b,k,n)`, enquanto o shift finito atua em
`Matrix (Fin N) (Fin N)`. O crosswalk operador continua sendo o próximo gate.

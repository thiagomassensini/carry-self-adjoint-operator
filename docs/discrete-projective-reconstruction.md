# Reconstrução fiel discreta–projetiva

Esta costura reúne o TFVD discreto, a reconstrução causal de brackets e a
equivalência da válvula projetiva no mesmo teorema sobre sequências inteiras.

Para um corpo `K` de característica zero e `f : ℕ → K`, escreva

\[
M_f=\operatorname{projectiveValveMass}
  \bigl(\operatorname{toProjective}(\operatorname{mk}(\Delta^2 f))\bigr).
\]

O teorema principal é

\[
f=g\iff f(0)=g(0)\ \land\ \Delta f(0)=\Delta g(0)\ \land\ M_f=M_g.
\]

A massa recupera exatamente a curvatura. Os dois dados de bordo recuperam a
parte afim. Em conjunto, eles determinam o estado inteiro.

## Equivalência com inversa explícita

`DiscreteProjective.ReconstructionData K` guarda valor inicial, inclinação
inicial e uma massa formal normalizada. `reconstructionEquiv` identifica
canonicamente esse tipo com `ℕ → K`.

Para reconstruir uma sequência a partir de `(a,v,A)`:

1. extrair a curvatura formal `A' / A`;
2. transportá-la de volta à coordenada original;
3. usar seus coeficientes como bracket, com sementes `a` e `a+v`;
4. aplicar `causalBracketReconstruction`, já existente.

`mk_reconstruct_eq_green` identifica essa inversa com a fórmula Green:

\[
\operatorname{mk}(f)=\frac{a}{1-X}
+\frac{vX}{(1-X)^2}
+\frac{X^2}{(1-X)^2}
  \operatorname{fromProjective}\!\left(\frac{A'}{A}\right).
\]

Os dois percursos são `reconstruct_encode` e `encode_reconstruct`.
`existsUnique_state_of_boundary_and_mass` reúne existência e unicidade.

## Compilação local

Primeiro, compilar apenas o novo módulo e sua auditoria:

```bash
lake build --wfail CarrySelfAdjointOperator.DiscreteProjectiveReconstructionAudit
```

Depois, conferir a integração com o repositório:

```bash
bash scripts/audit.sh
```

O agregador público importa o novo módulo, e `scripts/audit.sh` executa sua
auditoria antes da camada espectral. As dependências existentes permanecem
fixadas; não é necessário executar `lake update` para esta alteração.

## Escopo matemático

As declarações tratam de séries formais e sequências sobre um corpo de
característica zero. A construção reaproveita a reconstrução causal e a
equivalência curvatura–massa; não introduz uma recorrência substituta.

O resultado não exige hipóteses sobre zeros ou positividade espectral. A
identificação futura dessa massa com um germem analítico ou com um kernel
positivo específico precisa de sua própria demonstração.

## Validação desta PR

O código foi revisado contra as assinaturas das dependências no commit base.
A compilação Lean deve ser executada pelo servidor local e pelo CI: o
ambiente de autoria desta PR não possui Lean/Lake instalado.

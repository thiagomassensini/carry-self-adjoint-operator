# Checkpoint 001 — arquitetura mínima do fechamento

Data: 2026-09-16

## Corpus lido

Este checkpoint foi extraído somente de `gitignore/FECHAMENTO_FORMALIZAR/`.
O ponto terminal da sequência é:

- `FIVE_FIELD_CUBIC_TAU_CAPSTONE.md`;
- `FIVE_FIELD_CAPSTONE_LEAN_BLUEPRINT.lean`;
- `five_field_capstone_audit.json`.

Os documentos de três e quatro campos foram tratados como etapas históricas:
o primeiro não absorve o setor Stokes-normal; o segundo identifica um campo
quadrático universal, mas o capstone final volta a manter os dois canais
Stokes completos `S_1` e `S_2`.

## Teoremas mínimos extraídos

1. `threeGreenReadout` é o readout linear exato da ordem de canais
   `Yplus, Yminus, C1, X1, C2, X2` pela matriz racional `R3`.
2. `stokesNormalReadout` é o readout linear exato da ordem de canais
   `S10, S11, S12, S20, S21, S22` pela matriz racional `RS`.
3. `capstoneRHS` é a soma do tensor endpoint com os dois readouts.
4. O único teorema que ainda conecta o tensor físico da tau ao lado direito é
   uma ponte analítica externa. As notas a classificam como estruturalmente
   exata, mas os artefatos disponíveis neste diretório só fornecem a auditoria
   numérica do ponto físico; eles não fornecem uma prova Lean dessa ponte.

## Fronteira lógica

Não será introduzido um axioma silencioso para substituir a ponte física.
Primeiro será formalizada a camada algébrica independente:

- tipos dos estados de canais;
- matrizes `R3` e `RS`;
- igualdade entre os readouts coordenados e os produtos matriciais;
- composição do lado direito do capstone.

Depois será exposta, com nome próprio, a hipótese mínima da ponte física.
Assim fica claro exatamente qual teorema analítico ainda falta e nenhum audit
numérico será promovido indevidamente a theorem.

## Próximo passo

Criar `FiveFieldCapstoneMinimal.lean` neste mesmo diretório, importar apenas
`Mathlib`, reproduzir o blueprint Lean e provar a álgebra de readout com
`ext`, `fin_cases`, `simp` e `ring`.

Validação esperada:

```text
lake env lean gitignore/FECHAMENTO_FORMALIZAR/FiveFieldCapstoneMinimal.lean
```

Este arquivo é o primeiro checkpoint persistente da formalização.

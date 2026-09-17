# Checkpoint 007 — ponte algébrica dos dois campos Stokes

## Estado

O módulo

`CarrySelfAdjointOperator/FiveFieldStokesCumulativeReadout.lean`

compila com `lake build --wfail`.

## Resultado formal

Foram definidas:

- `stokesCumulativePair`, que empacota as três cumulativas de cada um dos
  dois campos completos na ordem
  `S10,S11,S12,S20,S21,S22`;
- `stokesGammaCumulativeReadout`, que aplica os três pesos de abertura
  `γ₋−γ₀`, `γ₀−γ₁`, `γ₁` a um único vetor cumulativo;
- `stokesCumulativeFieldPair`, a composição dessas duas construções com
  `stokesCumulativeChannels`.

Os theorems compilados são:

1. `stokesCumulativeReadout_pair_eq_gammaCumulativeReadout`:
   o readout dos seis canais é exatamente o readout do vetor
   `v₁ • S₁ + v₂ • S₂`;
2. `stokesCumulativeReadout_pair_eq_cubicPolarization`:
   o mesmo readout é a polarização cúbica de
   `stokesNormalReadout`;
3. `stokesCumulativeReadout_fieldPair_eq_singleFieldReadout`:
   a versão para dois campos abstratos integrados;
4. `stokesCumulativeReadout_fieldPair_eq_mixedField`:
   sob integrabilidade, o vetor cumulativo é o das densidades
   `v₁ f₁ + v₂ f₂`.

## Limite matemático preservado

Os campos `f₁` e `f₂` continuam sendo funções abstratas. Nenhum deles foi
identificado com a expressão física `Tr(Q_k Ψ E₂₁ Ψ⁻¹)`, nem foi assumida
integrabilidade física. A etapa restante é uma ponte analítica explícita
para essas duas funções e para os quatro coeficientes do tensor da tau.

## Próxima obrigação mínima

Formalizar a interface dos cinco campos em nível de funções/objetos, com
hipóteses explícitas de integrabilidade e com uma ponte de readout físico.
Essa ponte é a única parte que os artefatos classificam como teorema
analítico externo; os audits Python não podem ser usados como axiomas Lean.

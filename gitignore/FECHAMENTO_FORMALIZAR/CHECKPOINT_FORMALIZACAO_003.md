# Checkpoint 003 — dinâmica de jatos compilada

Data: 2026-09-16

## Arquivo criado

`FiveFieldCapstoneDynamicsMinimal.lean`

## Teoremas compilados

- `mixedYplus_transport`:
  a partir de `C'' - C/4 = G`, o jato de
  `Yplus = C + 2 C'` satisfaz
  `(Yplus)' - Yplus/2 = 2 G`;
- `mixedYminus_transport`:
  o jato de `Yminus = C - 2 C'` satisfaz
  `(Yminus)' + Yminus/2 = -2 G`;
- `singleJump_sum_transport`:
  as duas equações triangulares one-variable implicam
  `C' + X' = -C + 2 B`;
- `singleJump_equations_weighted`:
  para `t ≠ 0`, as equações triangulares podem ser multiplicadas por `t` sem
  esconder uma divisão.

Validação concluída:

```text
lake env lean gitignore/FECHAMENTO_FORMALIZAR/FiveFieldCapstoneDynamicsMinimal.lean
```

## Limite explícito

Os teoremas usam `MixedGreenSecondJet` e `SingleJumpChannelJet`. Isso é
intencional: o corpus fornece as equações, mas não fornece neste diretório uma
definição Lean dos campos analíticos com suas derivadas e condições de bordo.
O próximo fechamento deve tratar os canais Stokes como dados de estado e não
inventar uma primitiva analítica.

# Luna G — Fase A: transporte quantitativo do sinal C2

## Base e escopo

Trabalho isolado na branch `codex/luna-g-c2-energy-limit-2026-11-14`, baseada
no head do PR #117, `87e448a6c2fdd35b61cc3f6ff824bef9dc1b4b88`, que por sua vez
continua a cadeia #116 → #117. O checkout original não foi modificado.

Fixado `n`, sejam abreviações matemáticas para os objetos Lean originais

* `Q(n,k,x) := nativeSourceC2CentralLegReadout n k
  (nativeSourceC2TailCutoff n k) x`;
* `G(n,k,x) := nativeSourceGammaCorrectionGap n k x`;
* `E(2n,x) := nativeSourceFiniteBoundaryEnergy (2*n) x`.

O índice `n` é a ordem de Hankel, `k` é o índice radial e
`M(n,k) = nativeSourceC2TailCutoff n k` conta células C2. O corte diagonal
usa o orçamento exato `1/(k+1)`; não identifica o limite radial com o limite
de corte das células.

## Teoremas Lean provados

O novo módulo `CompletedNativeC2CentralLegEnergyLimit.lean` prova:

1. Para todo `n` fixo, eventualmente em `k` e uniformemente para todo vetor
   `x`,

   `|G(n,k,x) + 2*Q(n,k,x)| ≤ (1/(k+1))*‖x‖²`.

   Isso resulta da identidade exata do defeito finito
   `c2CarrierDefect = -2*Q`, do transporte no carrier original e do controle
   da cauda C2 exata no mesmo corte diagonal.

2. Para todo `η > 0`, eventualmente em `k` e uniformemente em `x`,

   `|8*Q(n,k,x) - E(2n,x)| ≤ (η + 4/(k+1))*‖x‖²`.

   A combinação usa literalmente
   `8Q-E = (-4G-E) + 4(G+2Q)`. O termo `|-4G-E|` vem de
   `rawGamma_chiralJetInput_eventually_energy_control`. A regularidade
   eventual dos nós fornece o strip e a não anulação do denominador original
   Hermite–Biehler exigidos pelo transporte; nenhum peso ou normalização foi
   alterado.

3. Para cada `ε > 0`, eventualmente em `k`, para todo `x`,

   `|Q(n,k,x) - E(2n,x)/8| ≤ ε*‖x‖²`.

   Esta é a convergência radial uniforme na bola unitária, para ordem `n`
   fixada. Não afirma uniformidade em `n` nem um limite transversal `d → 0`.

4. Se a forma de fronteira original tem margem `δ > 0`, então eventualmente
   em `k`,

   `(δ/16)*‖x‖² ≤ Q(n,k,x)` para todo `x`.

   Uma variante aceita como hipótese a positividade estrita da forma de
   fronteira e obtém a margem por compactação. Estas declarações não provam
   positividade da energia de fronteira.

## Certificados finitos e dependências

Os certificados existentes no Geometry of Numbers provam o par canônico
H6/K6 positivo a partir da fonte original (PRs #148, #323, #327 e #329).
Downstream PR [#331](https://github.com/thiagomassensini/geometry-of-numbers/pull/331)
restringe esse par pelas inclusões principais exatas `Fin.castLE` para cada
`n ≤ 6`, transporta o sinal pelo split original par/ímpar da energia e aplica
o teorema genérico de margem acima. Seu resultado compilado dá, para cada
`1 ≤ n ≤ 6`, uma constante `δ_n > 0` e positividade radial eventual do
readout C2 centro + pernas no corte exato `M(n,k)`. A constante pode depender
de `n`; as dimensões cobertas são 2, 4, 6, 8, 10 e 12.

O grafo de imports permanece acíclico: o transporte genérico fica no
repositório self-adjoint e a instanciação dos certificados fica downstream no
Geometry of Numbers. PR #331 é baseado em `main` desse repositório e depende
explicitamente do PR #118; foi compilado contra o commit `a90e84a` do PR #118.

## Hipóteses e limites

O resultado geral de transporte requer o sinal da energia finita somente para
deduzir sinal positivo de `Q`. Ele não afirma positividade de Hankel
incondicional nem oculta a hipótese `InfinitePositiveRealNativeZeros` em
consumidores de positividade estrita. O sinal centro + pernas está agora
certificado nas ordens 1–6 por PR #331; a obrigação geral de E4 permanece
aberta para `n ≥ 7`. O erro da cauda C2 não é mais uma hipótese.

Nenhuma nova suposição de convergência, novo axioma, `sorry` ou `admit` foi
introduzido. Os pesos e estados do carrier original, os cruzamentos e a
completion permanecem os declarados pelos módulos anteriores.

## Verificação

- `lake build --wfail`: passou, 10.239 tarefas Lean.
- O módulo de transporte e seu audit foram compilados com
  `-DwarningAsError=true`.
- `#print axioms` nas cinco declarações novas reporta apenas
  `propext`, `Classical.choice` e `Quot.sound`.
- `git diff --check`: passou.

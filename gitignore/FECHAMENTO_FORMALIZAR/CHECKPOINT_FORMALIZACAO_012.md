# Checkpoint 012 — cauda exponencial concreta do endpoint

Data: 2026-09-16

## Contexto recuperado

A skill `genuine-first` passou a estar disponível em
`/home/thlinux/.codex/skills/genuine-first/SKILL.md`.
Foram lidas a skill e as seções pertinentes de `references/theory.md` sobre
câmeras, escalar comum, operador finito, momentos nativos e distinção entre
equivalência linear e identificação métrica. Isso resolve a indisponibilidade
registrada nos checkpoints 010–011; não altera retroativamente o que fora lido.

O script anexado pelo usuário é byte a byte igual ao arquivo
`native_carry_r2_height_operator.py` já presente nesta pasta.
SHA-256: `853e19a5dd76a29deb1534e0079e332d65b94ffc33047c5f3cc84c036e27fa50`.
Ele foi inspecionado, não executado como justificativa de theorem.

O dicionário observado é: brackets finitos + cauda; divisão pelo fator da
câmera; completamento; coeficientes pares; recorrência de `-Phi'/Phi`; par
de matrizes de momentos; ortogonalização; operador simétrico e leitura
espectral. A remoção da câmera ocorre antes dos momentos. A coincidência
numérica dos autovalores não é usada como hipótese formal.

No Lean existente, `NativeMomentProjectiveValveBridge.lean` distingue
explicitamente `completedNativeEvenFormalSeries` da série dos momentos e
prova `derivative_completedNativeEvenFormalSeries`. Essa identidade não é
por si só a realização Gram geométrica dos momentos.

## Novo módulo

`CarrySelfAdjointOperator/FiveFieldChiralEndpointTail.lean`.

Provados, sem hipótese física:

1. integrabilidade de `exp(-s)*s^m` em `(x,infinito)` para todo `x : Real`;
2. recorrência da integral por integração por partes;
3. `E_m(x)=exp(x)*integral_x^infinito exp(-s)*s^m ds`;
4. versão complexa, com a mesma medida de Lebesgue;
5. passagem para qualquer soma finita de coeficientes complexos;
6. composição com a dualidade já provada:
   `alpha_R+(x+1)*beta_R = exp(x)*integral_x^infinito exp(-s)*R(s) ds`
   quando `x=t1` ou `x=t2`.

Há sete declarações de theorem, incluindo os lemas auxiliares de
integrabilidade e as versões real/complexa. As três primeiras seções da nota
`CHIRAL_ENDPOINT_THEOREM_FROM_DARBOUX_ORTHOGONALITY.md` agora têm sua etapa
algébrica e a realização analítica da cauda formalizadas.

Validação concluída: `lake env lean` do módulo, `lake build --wfail
CarrySelfAdjointOperator.FiveFieldChiralEndpointTail` e `lake env lean` de
`FiveFieldChiralEndpointTailAxioms.lean` passaram. Todos os sete teoremas
retornaram somente `[propext, Classical.choice, Quot.sound]`.

## Próxima obrigação examinada

A seção 5 das notas identifica a cauda do polinômio físico com um pareamento
simplético; a seção 6 usa o pullback do Jacobiano físico. A busca atual nos
módulos Lean não encontrou essa realização concreta. Não se pode substituí-la
pelo Jacobiano numérico do script.

As notas de monodromia decorada contêm, entretanto, uma etapa matricial
exata anterior: `X(eta)^2=0` e a identidade local de traço de
Kirillov–Kostant. O script correspondente verifica-a simbolicamente. Essa
etapa local pode ser formalizada sem extrair coeficientes numéricos e sem
declarar o pullback global provado. Ela é o próximo teste escolhido.

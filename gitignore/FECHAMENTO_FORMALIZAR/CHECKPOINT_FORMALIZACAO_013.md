# Checkpoint 013 — órbita local decorada explícita

Data: 2026-09-16

Novo módulo: `CarrySelfAdjointOperator/FiveFieldDecoratedLeveltLocal.lean`.
Fontes: `MONODROMIA_DECORADA_E_PARES_DARBOUX_LOCAIS.md` e
`native_carry_decorated_monodromy_darboux_lab.py`.

## Avanço concreto

A matriz `X(eta)=[[-eta,1],[-eta^2,eta]]` foi definida explicitamente.
Foram provados a conjugação pela matriz unipotente inferior, `X^2=0` e
`X*v=0 iff v_1=eta*v_0`.

O resíduo `N=kappa*a*X` também é explícito. Suas derivadas complexas em
amplitude e decoração foram verificadas com `HasDerivAt`; os dois
comutadores das notas coincidem com essas tangentes. Para `a != 0`,
o coeficiente de traço local é exatamente:

`trace (N * [X_a,E21]) = -kappa`.

O módulo anterior de obstrução adjunta foi reutilizado para provar que um
autovetor de `ad_N` com autovalor não nulo deve ser zero, agora para este
resíduo concreto e não apenas para uma matriz quadrado-zero abstrata.

São onze teoremas. Não foram extraídos coeficientes numéricos, nem assumido
o pareamento como hipótese. A norma matricial elemento a elemento é usada
localmente para as derivadas; não foi alterado nenhum carrier anterior.

## Escopo

Isto é a normalização da órbita **local**. Não é uma prova de redução global,
do pullback do Jacobiano físico ou da ponte entre caudas e amplitudes.
As notas posteriores explicitam um termo de fusão, cujo cálculo matricial
é o próximo passo escolhido.

## Validação

`lake env lean CarrySelfAdjointOperator/FiveFieldDecoratedLeveltLocal.lean`
passou sem avisos. `lake build --wfail
CarrySelfAdjointOperator.FiveFieldDecoratedLeveltLocal` também passou.
`FiveFieldDecoratedLeveltLocalAxioms.lean` auditou os onze teoremas:
todos retornaram somente `[propext, Classical.choice, Quot.sound]`.

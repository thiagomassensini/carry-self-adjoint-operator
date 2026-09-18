# Checkpoint 010 — retomada genuine-first e endpoint da recorrência

Data: 2026-09-16

## Correção de contexto

A construção nativa não deve ser redefinida por uma identidade externa com
zeta/Xi. `CompletedNativeCharacteristic.lean` define a característica por
cabeça finita e cauda exata de células. `CompletedOperatorCharacteristic.lean`
aplica ao escalar nativo o fator de completamento arquimediano; a definição
não chama a função Xi de Riemann.

Na seção 7 de `TEORIA_GEOMETRICA_DO_CARRY_E_OPERADOR_ORTOGONAL_MULTIBASE.md`,
`F_p(s) = 1 - p^(1-s)` é o fator de calibração da carta, distinto da
característica. Não usar a letra `F` sem indicar qual objeto representa.
Nenhuma definição anterior será alterada por esta retomada.

A skill indicada pelo usuário como `Genuine First`, arquivo `theory.md`, não
foi localizada nas pastas locais consultadas. Não alegamos tê-la lido. A
orientação nativa acima foi conferida nas notas e nas definições existentes.

## Revisão do checkpoint 009

A última frase do checkpoint 009 era forte demais: a falta de definições
físicas em Lean não implica que continuar com as notas exija assumir o
capstone. Há derivações simbólicas anteriores ao capstone ainda por traduzir.
O fechamento físico completo continua pendente, mas é possível avançar
provando essas etapas sem novo axioma.

## Próximo passo mínimo escolhido

Fonte: seções 1–3 de
`CHIRAL_ENDPOINT_THEOREM_FROM_DARBOUX_ORTHOGONALITY.md`, conferidas com
`native_carry_chiral_endpoint_theorem.py` e
`HUMBERT_MOMENT_RECURRENCE_TWO_BASE_GERMS.md`.

Formalizar explicitamente as sequências homogêneas `f_m`, `g_m` com dados
iniciais `(1,0)`, `(0,1)` e a recorrência de três termos das notas, incluindo
o caso inicial `u_2 = (2+S)u_1 - (S+P)u_0`.

Definir o polinômio de endpoint por `E_0(x)=1` e
`E_(m+1)(x)=(m+1)E_m(x)+x^(m+1)`; provar o resíduo
`x^m (x-t1)(x-t2)` e, em toda ordem, a identidade
`f_m + (x+1)g_m = E_m(x)` quando `x=t1` ou `x=t2`.

Provar em seguida a consequência para uma soma finita de coeficientes.
Não pressupor ortogonalidade Darboux, identificação de caudas com amplitudes,
ou a conclusão física. A representação por integral de cauda é uma etapa
posterior, não uma igualdade implícita na definição de `E_m`.

Status neste checkpoint: plano e fontes fixados; validação Lean será
registrada em checkpoint posterior.

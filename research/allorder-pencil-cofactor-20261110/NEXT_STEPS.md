# Próximas etapas

- [x] CHECKPOINTS 1–2: provar o pencil-cofactor e a energia do vetor crítico para dimensão arbitrária, sem inversa.
- [x] CHECKPOINT 3: compor a energia com a integral bordeada e registrar apenas a equivalência condicional de sinais.
- [ ] CHECKPOINT 4 (frente separada): provar o lema genérico de Desnanot–Jacobi sem inversibilidade; especializar a Hankel. A base `n=1` já compila.
- [x] PRIORIDADE 2: formalizar o teto característico de Schur para qualquer `s,n`; os próximos coeficientes são `c_(2n+1)` na torre central e `c_(2n+2)` na deslocada.
- [x] PRIORIDADE 3 (ponte finita): identificar os discriminantes nativos 4×4 com `16 * det(G_{0,4})` e `16 * det(G_{1,4})`; provar o sinal central pelo certificado de ordem 14 e deixar o shifted como condição exata sobre `c₈`.
- [x] PRIORIDADE 3 (gate central seguinte): provar o gate Euler par de `n=3` a partir do certificado fonte-first central de ordem 14, sem supor `PosDef(G_{0,4})`.
- [x] CHECKPOINT 5: compor com a indução Schur/Euler existente; o corolário é explicitamente condicional às massas.
- [x] MISSÃO A: obter `c₀>0` internamente pelo teorema CSA; axiomas auditados.
- [x] MISSÃO B: fechar os dois gates Euler em `n=2` com os certificados fonte-first de ordem 10/12, sem assumir `PosDef` 3×3.
- [x] MISSÃO C: auditar os incrementos de massa entre `n=2` e `n=3`; o resto par `R_{0,3}` agora é positivo pela face fonte de ordem 14, enquanto o ímpar permanece equivalente ao teto de `c₈`.
- [ ] Provar por estimativa fonte-first o gate ímpar `n=3`, `c₈ < nativeSourceCharacteristicCeiling 1 3`; correlacionar explicitamente esse teto genérico ao teto de fronteira `nativeSourceEightCharacteristicCeiling` e, depois, buscar os gates das ordens seguintes.

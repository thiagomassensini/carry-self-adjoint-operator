# Próximas etapas

- [x] CHECKPOINTS 1–2: provar o pencil-cofactor e a energia do vetor crítico para dimensão arbitrária, sem inversa.
- [x] CHECKPOINT 3: compor a energia com a integral bordeada e registrar apenas a equivalência condicional de sinais.
- [ ] CHECKPOINT 4 (frente separada): provar o lema genérico de Desnanot–Jacobi sem inversibilidade; especializar a Hankel. A base `n=1` já compila.
- [x] PRIORIDADE 2: formalizar o teto característico de Schur para qualquer `s,n`; os próximos coeficientes são `c_(2n+1)` na torre central e `c_(2n+2)` na deslocada.
- [x] PRIORIDADE 3 (ponte finita): identificar os discriminantes nativos 4×4 com `16 * det(G_{0,4})` e `16 * det(G_{1,4})`; provar o sinal central pelo certificado de ordem 14 e deixar o shifted como condição exata sobre `c₈`.
- [x] CHECKPOINT 5: compor com a indução Schur/Euler existente; o corolário é explicitamente condicional às massas.
- [x] MISSÃO A: obter `c₀>0` internamente pelo teorema CSA; axiomas auditados.
- [x] MISSÃO B: fechar os dois gates Euler em `n=2` com os certificados fonte-first de ordem 10/12, sem assumir `PosDef` 3×3.
- [x] MISSÃO C: auditar os incrementos de massa entre `n=2` e `n=3`; as comparações exatas equivalem aos restos ainda abertos `R_{0,3}>0` e `R_{1,3}>0`.
- [ ] Encontrar certificados fonte-first para esses restos ou para as desigualdades de massa de ordem 3 em diante.
- [ ] Não confundir a ponte deslocada 4×4 com seu sinal: provar independentemente `c₈ < nativeSourceEightCharacteristicCeiling` ou uma desigualdade de massa de força equivalente.

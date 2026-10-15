# Reaproveitamento geométrico para a positividade da fonte

Estudo de 14 de outubro de 2026. Fontes no servidor `llm`; base do repositório `carry-self-adjoint-operator`: `486fb5184d7a52d6054edf3c9837d7d76d7aca47` (PR #94). O inventário anexo registra 13 repositórios. A leitura e as recompilações foram seletivas: este documento não representa uma auditoria de todos os teoremas desses repositórios.

## Resultado principal

**Já existe na teoria um mecanismo geométrico de positividade estrita, anterior à realização dos momentos.** Em `primos`, o mapa de análise prime-carry do estado nativo satisfaz uma contração uniforme `11/12`. Consequentemente, a energia complementar é positiva para todo estado não nulo. Esse resultado já está no pin efetivamente consumido pelo autoadjunto; utilizá-lo não exige atualizar dependências.

**Ainda falta identificar essa energia com a energia da fonte completada.** A contração não afirma que os momentos canônicos são o Gram complementar. Os resultados novos de projeção polarizada, reconstrução com bordo e gluing tornam essa obrigação mais concreta, mas não a resolvem automaticamente. A positividade nativa para N arbitrário continua aberta.

## 1. O mecanismo que já está formalizado

Em [CpNativeGprePrimeCarryContraction.lean, pin consumido](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpNativeGprePrimeCarryContraction.lean), temos

\[
C:\mathrm{NativeGpreTowerHilbert}\longrightarrow
\mathrm{PrimeCarryDefectGlobalHilbert},
\qquad \|CX\|^2\leq\frac{11}{12}\|X\|^2.
\]

Os nomes Lean são `nativeGprePrimeCarryDefectState` e `nativeGprePrimeCarryDefectState_norm_sq_le`. Cada câmera lê o **mesmo** estado X por seu perfil geométrico; a coordenada prime-carry é essa leitura multiplicada pelo eixo dual fixo da câmera. X não é definido por inversão de uma matriz dos momentos desejados.

A majorante combina a contribuição da câmera 2, limitada por `13/24`, com a cauda ímpar, limitada por `3/8`. A soma é `11/12`; a prova usa estimativas e somação telescópica, sem hipótese de zero, de sinal dos momentos ou de realização da característica.

Portanto, a forma real

\[
\mathfrak d(X,Y)=\langle X,Y\rangle-\langle CX,CY\rangle
\]

satisfaz

\[
\boxed{\mathfrak d(X,X)\geq\frac1{12}\|X\|^2,}
\qquad X\ne0\Longrightarrow\mathfrak d(X,X)>0.
\]

Na versão mais recente de `primos`, [CpNativeGprePrimeCarryDefectForm.lean](https://github.com/thiagomassensini/primos/blob/8c4b7fdf65a49d1d0febe8193d56e2cfb2191260/CPFormal/Analytic/CpNativeGprePrimeCarryDefectForm.lean) já empacota esse mesmo mapa como operador real linear e prova a coercividade da forma. Não precisamos inventar uma nova métrica positiva. No pin antigo, duas consequências locais de auditoria verificam diretamente a margem e a estrita positividade usando a contração existente.

**Atenção ao significado de “momento”:** `nativeGprePrimeCarryDefectState_realizes` exige `IsNativeGprePrimeMomentRealizationAt 1 (3*M) s X`. Ali as leituras são indexadas pelas câmeras primas. Essa hipótese não identifica a leitura com `canonicalCompletedNativeLogDerivativeMoment n`, indexada pela ordem do jato. Confundir esses dois índices esconderia justamente a ponte em aberto.

## 2. Cruzamentos e resíduos já têm uma API adequada

O mesmo módulo recente define `primeCarryActiveProjection S`, a projeção ortogonal sobre um atlas finito de eixos prime-carry. Já estão formalizados idempotência, autoadjunção, ortogonalidade ao residual e a identidade **polarizada**

\[
\langle X,Y\rangle
=\langle PX,PY\rangle+\langle X-PX,Y-PY\rangle.
\]

Ela vale para duas entradas independentes, sem hipótese de realização dos momentos. Isso conserva os cruzamentos e fornece uma ferramenta melhor que conferir apenas a energia diagonal. A identificação de PX com o estado de proveniência canônico, entretanto, continua dependendo de `realizesOn`. O teorema de Pitágoras do ledger TFVD/Bessel também explicita essa hipótese; não a fornece.

O módulo [CpNativeGpreCorrectedWedgeTowerGluing.lean](https://github.com/thiagomassensini/primos/blob/8c4b7fdf65a49d1d0febe8193d56e2cfb2191260/CPFormal/Analytic/CpNativeGpreCorrectedWedgeTowerGluing.lean) constrói vetores geométricos corrigidos para cada câmera e prefixo. Seu residual é exatamente

\[
\langle h_{p,\tau},X\rangle-
\mathrm{GreenBulk}_{p,\tau,M,s},
\]

e equivale ao pareamento do perfil com a diferença entre X e a fonte corrigida daquela câmera. O residual da própria fonte, em sua própria câmera, é zero. Isso não constitui um único estado X que funcione simultaneamente em todas as câmeras. A API permite manter essa diferença explícita em vez de descartá-la durante a síntese.

## 3. O domínio correto precisa conservar o bordo

A versão atual de `geometry-of-numbers` contém um estado concreto que merece ser reaproveitado: [BaseTwoCompletedBoundaryHilbert.lean](https://github.com/thiagomassensini/geometry-of-numbers/blob/e1084b43533255b399b82dc307b536d7dfdca07f/GeometryOfNumbers/Analysis/BaseTwoCompletedBoundaryHilbert.lean). O espaço é

\[
\mathbb C\oplus_2\bigl(\mathrm{MaterialEdgeL2}\oplus_2\mathbb C\bigr),
\]

com seed, interior material e retorno da célula inteira. O retorno vem do limite dos prefixos geométricos. Há convergência no espaço de Hilbert e um funcional limitado que recupera o sinal completo **antes do dressing**: `baseTwoCompletedBoundaryHilbertReadout_eq_signal`.

O motivo para conservar essa coordenada é matemático: [BaseTwoRawL2ReadoutNonclosable.lean](https://github.com/thiagomassensini/geometry-of-numbers/blob/e1084b43533255b399b82dc307b536d7dfdca07f/GeometryOfNumbers/Analysis/BaseTwoRawL2ReadoutNonclosable.lean) prova que o readout bruto no espaço somente de arestas materiais não é sequer fechável. Há entradas tendendo a zero em norma com leitura constante 1. Logo, uma extensão por continuidade nesse domínio perderia informação essencial.

Esse impedimento é específico do readout bruto no domínio sem bordo. Ele não invalida a realização aumentada acima. Também não identifica esse espaço complexo com `NativeGpreTowerHilbert`: **o transporte entre os dois ainda precisa ser construído e verificado**, incluindo parâmetros, completação e conexões de derivação.

O módulo `BaseTwoCompletedVectorLiftGate` explicita o dressing escalar e seu termo de conexão. `CanonicalGreenMomentJetSeam` mostra que um mesmo transporte Parseval conserva o pareamento e o residual da primeira coluna; ele não elimina esse residual. `CompleteVerticalObservationGram` dá injetividade e um Gram positivo da observação completa, que ainda não é o Gram dos momentos canônicos.

## 4. Como isso se liga ao avanço theta/Green/válvula

O PR #94 já provou, para todo N, setor s e entrada real x,

\[
E_{s,N}(x)=\sum_{i,j<N}x_ix_jm_{i+j+s}
=\int_0^\infty
\mathscr L\!\left(\sum_{i,j<N}x_ix_jP_{i+j+s}\right)(u)A(u)\,du,
\quad \mathscr LP=P''-P/4.
\]

Aqui m é literalmente `canonicalCompletedNativeLogDerivativeMoment`, A é a cauda theta original e os P são os polinômios derivados da característica original. Os termos de bordo dessa identidade foram controlados para a síntese completa. A válvula fornece a convolução triangular exata desses P e comuta com a transferência diferencial. A densidade transferida pode ser negativa; a identidade não prova o sinal geral.

Uma obrigação concreta para explorar o mecanismo de `primos` seria construir, **a partir da fonte completada**, vetores reais \(U_{s,n}\) no espaço da torre e demonstrar

\[
\boxed{\mathfrak d(U_{s,i},U_{s,j})=m_{i+j+s},
\qquad s\in\{0,1\}.}
\]

Essa é uma proposta de alvo, não um resultado formalizado nem uma identificação garantida. O transporte pode revelar outra forma correta ou uma correção adicional. Ele deve ser derivado conservando seed, quatro setores, cruzamentos, retorno, cauda e dressing. Não se deve escolher U por uma fatoração dos próprios Hankel cuja positividade se quer provar.

Se essa igualdade for demonstrada, a bilinearidade e a contração já dão, para todo N,

\[
E_{s,N}(x)
=\mathfrak d\!\left(\sum_i x_iU_{s,i},\sum_i x_iU_{s,i}\right)
\geq\frac1{12}\left\|\sum_i x_iU_{s,i}\right\|^2.
\]

A positividade estrita exigirá também que uma combinação finita não nula não colapse nesse estado. A constante `1/12` está na norma da torre; **não é uma margem uniforme dos pivôs nativos**. As normas das sínteses podem ser muito pequenas. Portanto, essa estimativa por si só não explica numericamente o pivô da oitava fonte.

O primeiro teste dessa construção deve ser o kernel com duas entradas e a normalização exata das primeiras coordenadas, inclusive m₀ e m₁. A igualdade de um único readout \(\ell(U_n)=m_n\) não determina o produto interno entre os vetores. Também não basta anular o fluxo contínuo no centro para descartar o traço discreto TFVD: esses traços não foram identificados.

Uma rota alternativa é obter uma identidade com um defeito explícito e provar que sua parte negativa é menor que a margem disponível. Mesmo nessa rota, é necessário primeiro demonstrar a identidade com a **mesma fonte**; a desigualdade `11/12` não controla automaticamente um defeito de outro espaço.

## 5. Atalhos que as próprias fontes impedem

- **Interpolação finita por Riesz:** `CpNativeGpreFiniteTowerRieszSynthesis` realiza dados finitos de câmeras por inversão do Gram dos perfis. Isso não constrói por si só a fonte física comum nem o limite de energia. Em [CpNativeGpreFiniteGreenBulkRieszEnergy.lean](https://github.com/thiagomassensini/primos/blob/8c4b7fdf65a49d1d0febe8193d56e2cfb2191260/CPFormal/Analytic/CpNativeGpreFiniteGreenBulkRieszEnergy.lean), para M>0 e os parâmetros na faixa declarada, a energia dessa família mínima de leituras Green-bulk brutas é uniformemente limitada nos atlas finitos exatamente na linha crítica; nessa linha, essa família específica é zero. Isso impede promovê-la diretamente a um portador não nulo da primeira coluna. Não é impossibilidade de todo estado geométrico comum.
- **Gram estático de divisibilidade:** `native-carry-spectral-weyl` fornece o Gram exato `1/lcm(d,e)` e mantém os cruzamentos dos perfis. Não fornece a identificação dinâmica com os jatos da característica. Seus polinômios de hierarquia não são os P theta apenas por terem a mesma letra.
- **Quadro Green:** `GreenFrame.Concrete.seedResidualAnalysis_norm_sq_bounds` dá `‖f‖²/2 ≤ ‖Sf‖² ≤ ‖f‖²` no domínio próprio, com somabilidade e canais explícitos. Falta demonstrar que os canais da fonte completada correspondem aos dessa decomposição.
- **Válvula projetiva:** as identidades formais `G_q B_q + R_q Tr = I` e `X²/(1-X)²=Y²`, com `Y=X/(1-X)`, são úteis para reconstrução e transporte. O quadrado formal não é uma representação positiva da energia nativa. Profundidade formal X, coordenada projetiva Y, germen espectral z, variável theta u e altura precisam de mapas tipados entre si.
- **Resolvente em `momentos`:** o estudo confirma identidades finitas e defeitos de bordo do mesmo operador truncado. Seus certificados numéricos não demonstram convergência infinita nem a positividade prévia da fonte; o cálculo de `J^(-1/2)` depende do sinal de J.
- **Identidade refletida C3:** a igualdade finita entre traço do comutador e `-log(3)` vezes Green conserva as cunhas e a normalização. O sinal/zero desse traço finito não identifica o kernel canônico em todas as ordens.

## 6. Mapa dos repositórios consultados

Os commits completos, remotos e estados locais estão em `inventory.json`. “Fonte” abaixo significa leitura de módulos selecionados; “metadados” significa que nenhuma conclusão matemática foi extraída do conteúdo.

| Repositório | O que ajuda / limite | Verificação nesta investigação |
|---|---|---|
| `carry-self-adjoint-operator` | Ponte theta/Green/válvula e gates da primeira coluna | Nova auditoria nos pins reais e raiz/auditoria global compiladas |
| `primos` | Contração `11/12`, forma coerciva, projeção polarizada e residual de gluing | Três auditorias recentes compiladas; contração também auditada no pin consumido |
| `geometry-of-numbers` | Estado Hilbert com bordo e retorno; readout bruto não fechável; seam dos jatos | Quatro auditorias recentes compiladas |
| `green-frame-theorem` | Orçamento seed/residual com limite uniforme | Declaração auditada no pin consumido |
| `native-carry-spectral-weyl` | Gram estático de divisibilidade e perfis com cruzamentos | Fonte; sem novo build autônomo |
| `native-carry-c3-crosswalk` | Identidade Green refletida finita | Fonte; sem novo build autônomo |
| `momentos` | TFVD, válvula, relações entre variáveis e estudo finito do resolvente | Notas e resultados selecionados; sem certificação infinita nova |
| `teoria_dos_defeitos` | Compensação entre fonte/seed/carrier e avisos sobre cumulantes/Hankel | Notas; nenhum Lean rastreado nesse checkout |
| `genuine-zero-uniform-atlas-energy` | Padrão torre/cauda/transversal; coercividade com hipóteses próprias | Fonte; não fornece a identificação da energia canônica |
| `genuine-riemann-zeta-transfer` | Transferência da característica nativa para zeta e orçamento estrutural | Fonte; não fecha o Gram positivo requerido |
| `carry-geometry` | Rigidez da amplitude quadrática na geometria posicional | Fonte; sem identificação com momentos |
| `finite-native-carry-operator` | Referência do operador finito | Metadados |
| `formalizacao_C2` | Checkout com extensa pesquisa preexistente | Metadados; 295 entradas locais preservadas |

Não alteramos fontes, pins ou branches desses outros repositórios. Os builds atualizaram somente caches ignorados. A única alteração de código desta tarefa é uma auditoria no autoadjunto, acompanhada deste estudo e de seus registros de proveniência.

## 7. Verificação reproduzível

No autoadjunto, mantendo todos os pins originais:

```text
lake build --wfail CarrySelfAdjointOperator.GeometricPrimeCarryReuseAudit
  sucesso: 9848 jobs
lake build --wfail CarrySelfAdjointOperator.GeometricPrimeCarryReuseAudit CarrySelfAdjointOperator CarrySelfAdjointOperator.Audit
  sucesso: 10352 jobs
```

A primeira guarda examina quatro raízes — duas consequências privadas locais e duas declarações já existentes — com fecho tipo/corpo de 2824 declarações. A segunda examina oito interfaces existentes com fecho de 6089 declarações. Ambas passaram. Os `#print axioms` das raízes mostraram somente fundamentos usuais do Lean (`propext`, `Classical.choice`, `Quot.sound`), sem `sorryAx`.

Na versão atual de `geometry-of-numbers`:

```text
lake build --wfail GeometryOfNumbers.Analysis.BaseTwoCompletedBoundaryHilbertAudit GeometryOfNumbers.Analysis.CanonicalGreenMomentJetSeamAudit GeometryOfNumbers.Analysis.CompleteVerticalObservationGramAudit GeometryOfNumbers.Analysis.BaseTwoRawL2ReadoutNonclosableAudit
  sucesso: 8818 jobs
```

Na versão atual de `primos`:

```text
lake build --wfail CPFormal.Analytic.CpNativeGprePrimeCarryDefectFormAudit CPFormal.Analytic.CpNativeGpreCorrectedWedgeTowerGluingAudit CPFormal.Analytic.CpNativeGpreFiniteGreenBulkRieszEnergyAudit
  sucesso: 3618 jobs
```

As versões atuais desses dois repositórios são mais recentes que os pins consumidos. Foram compiladas nos próprios checkouts, com seus manifestos; não foram silenciosamente incorporadas ao autoadjunto. Nenhum resultado numérico novo foi usado para inferir sinal em ordem infinita.

## Próximo alvo recomendado

Construir o transporte da fonte completada com bordo/retorno para o estado comum da torre, conservando o dressing e os jatos reais apropriados. Calcular o pareamento polarizado desse estado com a forma complementar já existente e comparar com o kernel canônico, começando pelas normalizações centrais. Se surgir um residual, mantê-lo como objeto explícito e estudar sua compensação geométrica.

Esse é um alvo mais específico que procurar uma medida positiva conveniente: a teoria já oferece uma forma estritamente positiva. O trabalho matemático pendente é provar que ela mede a energia da nossa fonte, ou localizar exatamente a correção que impede essa identificação.

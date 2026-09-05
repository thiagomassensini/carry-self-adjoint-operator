# Mapa: retorno misto e canais do trace completado

Data: 2026-09-05. Repositório: carry-self-adjoint-operator.
Base desta rodada: ea750d0629f25963c195db27972e415c3c02a01a,
descendente da base solicitada 225a85d9e8e3e0a3b659c5b6ad821458770b3195.
Branch: agent/c3-return-completed-trace.

**Resultado:** os mapas atuais não permitem transportar a energia de retorno
para o trace em todo o carrier. Uma direção de energia de retorno zero
altera o trace. A identidade canônica explicita o canal que falta:
g_2 junto com a cauda exata. Gamma/native Gram não foi identificado.
Não realizar merge com esse resultado.

## 1. Objetos e orientação

Não foi criado operador, Gamma, Jacobi, momento ou candidato a kernel.
Os pulsos abaixo são testes nos tipos existentes, não estados substitutos
para a construção nativa.

Escreva g_n(s)=positiveDirichletGradient s n e
ell_n(s)=positiveLogDirichletGradient s n.
No CanonicalCompletedC3HilbertState, os canais ordinário e log-jet
são duas cópias separadas do l2. O mapa existente greenPort 3 s state lê
apenas o canal ordinário:

$$
c=(r g_0,r g_1,r g_2;\ g_0,g_1,g_2),
\qquad r=3^{-\operatorname{criticalDisplacement}(\Re s)}.
$$

A ordem dos rótulos das seis câmeras é **2,3,4,5,6,7**:

| Coordenada ordinária | Câmera radial | Câmera horizontal | Trace do primeiro bloco |
| --- | --- | --- | --- |
| g_0 | 2 | 5 | coeficiente 0 |
| g_1 | 3 | 6 | coeficiente -1 |
| g_2 | 4 | 7 | coeficiente +1 |

c3GreenPort_canonicalPrefix_source prova que esse empacotamento do prefixo
canônico é exatamente canonicalCompletedC3SixCameraSource, sem confundi-lo
com o vetor de resultantes chi das notas dinâmicas.

## 2. O que cada readout lê

O retorno normalizado pela própria G-métrica é:

$$
R(c)=\frac{v_*^TGc}{\sqrt{278}}=\frac{\sqrt{278}}3g_1.
$$

Os readouts existentes em um bloco completo são:

$$
V_{\rm head}=1+g_2-g_1,\qquad L_{\rm head}=\ell_2-\ell_1.
$$

Em qualquer cutoff M, eles leem somente os índices 3m+1 e 3m+2.
c3ValueHead_add_blockInitial e c3LogJetHead_add_blockInitial
provam que uma variação no índice 3k não altera esses readouts.

A conclusão nova na família canônica é
**c3CanonicalRawValue_eq_return_add_cameraSeven_tail**:

$$
\boxed{
V_{\rm C3}(z)
=1-\frac3{\sqrt{278}}R(\operatorname{canonicalSource}(z))
+g_2(s(z))+\operatorname{realCpBracketCutoffTail}(3,1,s(z)).
}
$$

Aqui V_C3 é canonicalCompletedC3RawHeightValue, **não** a característica
vestida completedNativeOperatorCharacteristic. A normalização por
sqrt(278) é a existente; não foi ajustada a h_0.

c3CanonicalPrefix_completedTrace reutiliza os teoremas de cabeça+cauda
para recuperar o par (canonicalCompletedC3RawHeightCompanion,
canonicalCompletedC3RawHeightValue), em todo cutoff.
A rotação por i ocorre após somar os dois canais log-jet.

## 3. Dois testes diferentes

### Câmera 5: energia Gamma sem alteração do trace

O pulso ordinário inicial de amplitude a produz no porto:

$$
\delta c_0=(r a,0,0;\ a,0,0).
$$

A projeção de trace não o vê. A perna radial é conservada; não se testa uma
câmera isolada que viole a relação do porto.

Para a diferente de zero e z fora do eixo real,
c3InitialPulse_gamma_energy_pos prova que a imagem desse pulso pelo Gamma
existente tem energia positiva, usando apenas sua injetividade.

c3CanonicalInitialPulse_gamma_energy_pos especializa a
a=g_0(s(z)), não nulo na faixa Genuine.
c3CanonicalPrefix_initialPulse_completedTrace preserva o trace completado,
com as caudas originais explícitas, sob variações iniciais ordinárias e log-jet.

Isso identifica a direção que o trace omite. Não afirma que os cruzamentos
Gamma de uma decomposição sejam ortogonais ou tenham sinal favorável.

### Câmera 7: alteração do trace sem energia de retorno

O pulso ordinário no índice 2 de amplitude real a produz:

$$
\delta c_2=(0,0,r a;\ 0,0,a).
$$

Pela orientação já provada de GT-H:

$$
A\,G^{1/2}\delta c_2=0.
$$

É o conteúdo de c3LastPulse_returnCompression_zero.
Portanto também A* A anula o vetor whitened. Isso usa a matriz completa
de retorno, não apenas a projeção escalar no raio misto.

Em todo cutoff não vazio, esse pulso altera V_head em a e preserva L_head.
O endpoint **not_c3TraceVariation_bounded_by_returnEnergy** nega a existência
de qualquer C real finito tal que, para todo vetor ordinário real x de três
coordenadas,

$$
|x_2-x_1|^2
\le C\,\|A G^{1/2}(r x_0,r x_1,r x_2;\ x_0,x_1,x_2)\|_2^2.
$$

O testemunho é x=(0,0,1): lado esquerdo 1, lado direito 0.

not_c3CompletedValue_factors_through_mixedReturn prova ainda que nenhuma
função do retorno escalar recupera o valor completado para todos os estados
desse carrier, mesmo com uma cauda fixa arbitrária.

c3CanonicalCameraSeven_traceMismatch usa o próprio g_2(s(z)):
subtraí-lo do prefixo mantém o retorno e altera o valor completado em -g_2,
provadamente não zero na faixa Genuine, em todo cutoff M>0.

**Alcance essencial:** o vetor perturbado não é apresentado como outro estado
canônico nem como uma mudança física de cutoff. As caudas são mantidas
explicitamente no teste das direções do carrier. Os resultados de não
fatoração e ausência de estimativa são sobre o carrier, não uma prova de
impossibilidade de todo acoplamento sobre um subespaço causal.

## 4. Cruzamentos de bordo

Use a orientação existente
greenForm(t_x,t_y)=conj(V_x) C_y-conj(C_x) V_y,
com t=(C,V) e C=i(L_head+L_tail).

c3CompletedTrace_lastPulse_boundaryDifference prova:

$$
\operatorname{greenForm}(t_x+(0,a),t_y+(0,b))
-\operatorname{greenForm}(t_x,t_y)
=\bar a\,C_y-\bar C_x\,b.
$$

Os dois cruzamentos são preservados. O termo pulso-pulso é zero porque
seus companions são zero; não foi descartado por ser pequeno.
Todos os tails permanecem dentro de C_x e C_y.

## 5. Cadeia existente reutilizada

1. canonicalC3AllCutoffGreenPort_prefix_eq e
   canonicalCompletedOperatorC3State_eq_greenBoundaryPair: mesma fonte.
2. sixCameraReturnReadout_sourceMap: readout com normalização G.
3. sixCameraReturnCompression_annihilates_cameraSixZero: A e orientação GT-H.
4. canonicalC3AllCutoffValueHeadReadout_prefix_eq e
   canonicalC3AllCutoffLogJetHeadReadout_prefix_eq: heads reais do prefixo.
5. canonicalCompletedC3AllCutoffOnePointState_completedValue_eq e
   canonicalCompletedC3AllCutoffOnePointState_completedCompanion_eq: tails exatos.
6. canonicalC3SixCameraSourceMap_injective e carryGammaSource_injective:
   energia Gamma positiva do pulso não nulo.
7. A continuação escalar para completion e Wronskiano já está em
   CompletedC3FullWronskianOperatorCarrier.lean, especialmente
   completedGreenWronskian_eq_normalizedFullOperatorInner.
   Ela não é reprovida nem declarada positiva aqui.

## 6. Resultado para a rota

O transporte universal da métrica A* A para esse trace falha antes de qualquer
passagem ao limite: há um vetor de retorno nulo com trace variável.

Na família canônica, a identidade de valor explicita g_2+cauda e o canal
log-jet continua separado. Uma relação adicional de energia teria de
acompanhar esses canais e seus cruzamentos sobre a família causal.
A presente investigação não constrói nem postula tal relação.

A igualdade do Gamma canônico antigo com o kernel nativo permanece refutada
pelo módulo C3GammaCameraTraceObstruction da base. Uma simples mudança
isométrica de coordenadas não altera esse resultado. Isso não refuta a
existência de uma medida geométrica nativa construída com outro acoplamento
de readouts devidamente demonstrado.

Não há goal Lean aberto neste módulo. A identificação Gamma/native Gram
não foi obtida; o certificado HP não foi invocado.

## 7. Arquivos e validação

- Novo: CarrySelfAdjointOperator/C3ReturnCompletedTraceChannels.lean
  (22 teoremas).
- Integração: CarrySelfAdjointOperator.lean, Audit.lean,
  KernelConstructionAudit.lean.
- Evidências: research/c3-return-completed-trace-2026-09-05/.

Nenhuma hipótese matemática nova nos endpoints, nenhum pin alterado.
O resultado dos 14 estágios, axiomas transitivos e checks de proveniência
é registrado em verification.json; o log completo acompanha a entrega.

Validação concluída: **14/14 estágios**, sem warnings; os **22 teoremas**
têm apenas propext, Classical.choice e Quot.sound como possíveis axiomas
transitivos. Os **15 pins** estão nos commits do manifest e limpos;
git diff --check passou. Nenhum merge foi realizado.

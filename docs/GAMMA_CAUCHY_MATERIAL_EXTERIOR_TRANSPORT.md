# Transporte Green/Gamma para ports materiais, com exterior conservado

## Proveniencia e escopo

Base: `83b77dceb93235604881990458ce979d44367da3`, depois do PR #78.
Host efetivo: `ssh llm`; repositorio de trabalho:
`/home/thlinux/carry-gamma-cauchy-transport`.
Toolchain: `leanprover/lean4:v4.32.0`.

Pins mantidos, sem atualizacao de dependencias:

- NativeCarrySpectralWeyl: `298d83c9351e308a5213b9f5ac32e44087f98a9f`.
- NativeCarryC3Crosswalk: `150cfc7fb08da96bf8117f15869cc2b819d593c2`.
- CPFormal: `65d50f6db1208708e109982ba97e1d51d3039956`.

O anexo Investigacao_Transporte_Gamma_Cauchy_2026-10-12.md foi lido
integralmente. SHA256:
`4e079630363277c0a4da39b309c6cdca0125057bec39f6664c4f51e7fd153213`.
Os seus decimais e programa nao sao certificados Lean. Nenhuma avaliacao
numerica de F, zeta ou theta participa das novas provas.

Nao escalarizar antes da sintese completa. A costura finita do PR #78 e
reutilizada, nao substituida por uma metrica ajustada.

## Correcao obrigatoria de orientacao

No pin efetivo, `NativeCarrySpectralWeyl.Boundary.greenForm` e
`inner x.2 y.1 - inner x.1 y.2`. Para o par literal `(a,b)` isto e
o oposto da convencao do pedido:

\[
g((a,b),(a',b'))=\langle a,b'\rangle-\langle b,a'\rangle.
\]

Preservamos o mismatch JA definido no repositorio e o termo A do pedido:

\[
A=\gamma_k\Omega_k((v,\theta v),(v',\theta v'))-N(z,w),
\qquad\gamma_k=2i/(k+1).
\]

O resultado com os nomes existentes e, portanto,

\[
\boxed{\mathrm{Mismatch}=-M-A-v^*H\eta'+\eta^*Hv'-2N.}
\]

`nativeGammaMismatch_materialDefectLedger` prova esta identidade, sem
alterar o mismatch, a fonte ou qualquer normalizacao. A soma com os sinais
propostos no pedido e `g-N`; sua diferenca para o mismatch existente e
exatamente `-2g`. `nativeGammaMismatch_proposedLedger_iff` certifica que
os dois ledgers coincidem exatamente quando `g=0`.

`nativeGammaMismatch_proposedLedger_fails_at_witness` prova a falha
no par canonico em `4+i/8`, para TODO C e k. A prova usa a negatividade
estrita anti-Herglotz do bloco Cauchy original e a fonte canonica nao nula.
Nao e um impedimento ao transporte enriquecido: o ledger corrigido fecha.

## Projecao nativa

`nativeSixCameraSynthesis` sintetiza literalmente as cameras de labels
2,3,4,5,6,7 no carrier complexo nativo. A compatibilidade do Cauchy
realificado com multiplicacao por qualquer escalar complexo, inclusive i,
e demonstrada antes de construir `nativeComplexCauchy`.

`nativeSixCamera_adjoint_synthesis` identifica o adjunto Hilbertiano
da sintese complexa com o sixCameraGram original. O determinante e
4981760. Definimos apenas coordenadas na base fixada:

\[
\alpha=G^{-1}E^*,\quad P=E\alpha,\quad Q=I-P.
\]

`nativeSixCameraProjection_orthogonalProjection` certifica imagem,
idempotencia, simetria e ortogonalidade. `nativeSixCameraProjection_roundtrip`
e `nativeSixCameraProjection_metricLedger` dao, para entradas independentes,

\[
u=E\alpha(u)+Qu,\qquad
\langle u,u'\rangle=\alpha(u)^*G\alpha(u')+\langle Qu,Qu'\rangle.
\]

`nativeSixCameraSynthesis_pack` identifica o packing com o original
`canonicalC3SixCameraSourceMap`. As coordenadas sao as duas pernas do
`canonicalCompletedOperatorC3State`, na ordem do pedido. Na fonte canonica
`Qa_z=0`, mas `Qb_z` permanece um vetor independente no dominio.

## Testemunha C9 aplicada a fonte original

`nativeC9Exterior_literal`, `nativeC9_camera_analysis`,
`nativeC9Coordinates_exact`, `nativeC9Exterior_orthogonal` e
`nativeC9Exterior_norm_squared` certificam os coeficientes racionais
originais e a norma quadrada `9012/139`, usando os perfis periodicos nativos.

`nativeComplexCamera_Cauchy_integral` deriva, dos multiplicadores e da
isometria Naimark originais, a integral com denominador `z-1-log x`.
`nativeCauchyKernel_integrableOn` prova integrabilidade fora do eixo real;
`nativeCauchyIntervalIntegral_endpoint_zero` registra que incluir o endpoint
zero nao altera a integral de Lebesgue.

`nativeC9CauchyReadout_selectsCameraSix` prova para TODO vetor complexo c:

\[
\langle u_9^\perp,C_zEc\rangle=
\frac{-224I_3(z)+48I_4(z)+80I_6(z)}{139}\,c_4.
\]

Indice 4 significa label 6. As outras cinco colunas se cancelam.
`nativeC9Density_literal`, `nativeC9Density_mass_zero` e
`nativeC9Beta_real_density_interval` certificam a densidade por intervalos
e a subtracao de f(3). `nativeCauchyReal_strictMono` vale sob
`1+log 6+abs z.im < z.re`. `log_six_lt_two` prova o bound para especializar
o sinal positivo em `nativeC9WitnessPoint = 4+i/8`.

`nativeCanonicalGammaCoefficients_cameraSix` identifica a coordenada
com `positiveDirichletGradient (operatorHeightParameter z) 1`.
`positiveDirichletGradient_one_ne_zero` vale sempre que `Re s>0`, pela
comparacao estrita de `3^(-Re s)` e `2^(-Re s)`.
No ponto escolhido, `s=3/8+4i` pertence a genuineCriticalStrip.

O certificado prioritario final e
`originalCanonicalGammaCauchyTrace_hasExterior`:

\[
Q(\mathrm{canonicalCompletedC3GammaBoundaryState}(4+i/8)).2\ne0.
\]

Tambem foram provados o readout C9 nao nulo e a ausencia desse traco
no espaco das seis cameras. Nao foi utilizada uma fonte artificial e6.

## Lift material e reconstrucoes inteiras

`materialCameraLift` usa os coeficientes de `materialStencilPolynomial`
aplicado as seis finiteStencil originais, antes de consultar theta.
`materialStencilPolynomial_coeff_address` certifica a posicao material
`m=j+1`. C2 usa centros 4(m+1), nao os centros FULL-EVEN historicos.
`materialCameraPolynomial_C2` e `materialNaturalCameraPolynomial` conservam
as seeds, todos os centros e todos os raios, com o fator `(1-X^r)^2`.

A janela e `N=7C+3`. Para C>=1, `materialCamera_natDegree`,
`materialCamera_monic` e `materialCameraLift_maxDegreeMinor` certificam
os graus `(4C,3C,4C+1,5C+1,6C+2,7C+2)`, coeficiente lider 1 e minor
de determinante 1. O decoder extrai essas linhas fixadas. O lift e
injetivo para todo C>=1; em C=0, C2 e C3 tem a mesma seed, e a falha
de injetividade e explicitamente provada.

`gammaMaterialTransport` conserva o par fisico e AMBOS os exteriores:

\[
T(a,b)=\bigl(\mathrm{twoPortSynthesis}(J\alpha(a),J\alpha(b)),(Qa,Qb)\bigr).
\]

`gammaMaterialTransport_roundtrip` e `gammaMaterialTransport_injective`
certificam sua reconstrucao para todo C>=1 e k. O decoder fisico usa
os readouts da base radial original e seu Gram; nao define a entrada
material nem resolve o encoder fonte-jet por uma inversa.

`gammaMaterialTransport_metricLedger` conserva `Delta=G-J^*HJ` e os
produtos exteriores. No corte C=1, `G[0,1]=0` mas `K[0,1]=139/252`.
`materialCameraLift_literal_not_isometric` e a versao para reescalas
diagonais nao nulas certificam a obstrucao deste lift literal nesse corte.
Nao afirmamos impossibilidade de todos os transportes enriquecidos.

## Candidato independente e observabilidade

O primeiro port e `J c(z)`. `nativeGammaMaterialSecondPort` e
`J alpha(nativeCanonicalGammaCauchyTrace z hz)`, produzido pelo Cauchy
original SEM usar theta. A conclusao vetorial vem depois:

\[
\eta=s-\theta_kv,\qquad
\mathrm{twoPort}(v,s)-\mathrm{twoPort}(v,\theta_kv)=\mathrm{twoPort}(0,\eta).
\]

`gammaMaterialGraphDefect_faithful` prova que todos os probes se anulam
se e somente se eta inteiro se anula; formula e decoder sao expostos.
`gammaMaterialGraphDefect_vs_completedSource` identifica a igualdade
com a fonte completada apenas sob a regularidade radial ja exigida no PR #78.
Nao acrescentamos essas hipoteses aos transportes ou a testemunha Gamma.

`nativeGammaCameraDefects_faithful` audita os defeitos POR camera antes
da soma. `nativeGammaCameraWholePair_sum` identifica a sintese inteira.
`nativeGammaWholePair_camera_fourHeadTails` conserva todas as 36 duplas
ordenadas de labels e os quatro setores, com duas entradas independentes.
`nativeGammaMaterialProbes_headTail`, `gammaMaterialMetricFormDefect_headTail`
e `nativeGammaMismatch_materialHeadTailLedger` conservam a cauda em cada
produto fisico, para qualquer R. Q nativo e essa cauda sao objetos distintos.

## Capstone e fronteira

`nativeGammaObservableTransport_capstone` aplica os certificados ao
par Gamma literal e reune sua reconstrucao, o segundo port Cauchy,
fidelidade dos probes, mismatch corrigido e exterior canonico nao nulo.
`gammaMaterialFirstPort_SourceJet` faz uma extensao EXPLICITA por zero
para uma janela par, sem criar estado fisico. `gammaMaterialFirstPort_correctedGreen`
reutiliza a reconstrucao Green fisica com bulk, dois tracos e todos os residuos.
Esta rota radial NAO identifica o resolvente Gamma `V*(z-Y)^(-1)V`
com `(I-q M_u)^(-1)`.

`canonicalExterior_sectorZero_vectorNonzero` prova que o setor exterior
da forma pode ser zero mesmo com o vetor exterior canonico nao nulo.
Nenhuma igualdade de formas permite descartar esse vetor.

Permanecem abertos: o dicionario de referencia A entre o grafico radial
completado e a forma escalar native undressed, a anulacao efetiva de eta,
e os criterios globais de mismatch-zero em NativeSourceLocusGreenCompatibility
e NativeGreenInverseTraceSewing. Nao sao assumidos resolvidos. A testemunha
C9 exclui fechar a proxima costura descartando o complemento nativo.
Nao foram identificados os relogios, provada isometria universal,
completude Laguerre, suporte infinito ou positividade da forma quiral.

A primeira obrigacao global tipada continua sendo a anulacao de
`canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw`
para a familia original, equivalente ao criterio global de compatibilidade
ja existente. O ledger corrigido expoe essa obrigacao; nao exige ou prova
a anulacao de cada parcela separadamente. O exterior C9 nao nulo nao refuta,
por si so, a compatibilidade de FORMAS, pois seu setor canonico e zero.
Ele refuta descartar esse vetor em um certificado de igualdade vetorial.

## Hipoteses exatas

- Projecao e ledgers nativos: nenhuma regularidade de F; duas entradas independentes.
- Lift e decoder injetivos: C>=1. C=0 e explicitamente degenerado.
- Cauchy original e sua integral: Im z!=0.
- Sinal de beta: Re z>1+log 6+abs(Im z), alem do dominio Cauchy.
- Gradiente canonico C6 nao nulo: Re(operatorHeightParameter z)>0.
- Ponto 4+i/8: todas essas condicoes e genuineCriticalStrip foram provadas.
- Comparacao com a fonte chiral completada: F e a coordenada positiva
  Hermite-Biehler nao nulos em TODOS os nos radiais da janela.
- SourceJet e Green radial corrigido: identidade algebrica do encoder;
  para o Green, 0<q<1. Nao se exige amplitude nao nula.
- Identificar N(z,w) com o nativeUndressed: os parametros de altura de z e
  w devem pertencer a genuineCriticalStrip, conforme o teorema existente.
  Fora dessa identificacao, N significa literalmente a forma estruturada
  `canonicalCompletedC3NativeSourceLocusScalarGreenForm`, nao uma extensao
  da igualdade undressed para fora de seu dominio certificado.
- Reutilizar o produtor TFVD completado do PR #78 exige sua faixa radial
  genuineCriticalStrip e regularidade. Nao foram identificados os estados
  TFVD/Green radial e Gamma/Naimark apenas por compatibilidade de readouts.

As formulas puramente algebricas de eta, probes, referencia e mismatch
nao interpretam um quociente em seus zeros como uma resposta fisica regular.
Essa interpretacao e feita somente no teorema com a regularidade explicita.

## Arquivos e teoremas principais

Todos os arquivos abaixo estao em `CarrySelfAdjointOperator/` e possuem
um arquivo `Audit.lean` correspondente. A lista COMPLETA das declaracoes
publicas, incluindo definicoes e adaptadores, esta no registro JSON.

| Modulo | Certificado principal |
| --- | --- |
| NativeGammaCameraComplexLinear | nativeComplexCauchy_I; nativeSixCameraAnalysis_synthesis |
| NativeGammaCameraAdjoint | nativeSixCamera_adjoint_synthesis; nativeSixCameraProjection_orthogonalProjection |
| NativeGammaSixCameraProjection | nativeSixCameraProjection_roundtrip; nativeSixCameraProjection_metricLedger |
| NativeGammaCauchyIntegral | nativeComplexCamera_Cauchy_integral; nativeCauchyKernel_integrableOn |
| NativeGammaC9Exterior | nativeC9Exterior_norm_squared; nativeC9CauchyReadout_selectsCameraSix |
| NativeGammaC9Analytic | nativeC9Beta_real_pos; nativeC9Beta_witness_ne_zero |
| NativeGammaC9Density | nativeC9Density_mass_zero; nativeC9Beta_real_density_interval |
| NativeGammaCanonicalSource | nativeSixCameraSynthesis_pack; nativeCanonicalGammaCoefficients_cameraSix |
| NativeGammaCanonicalExteriorWitness | originalCanonicalGammaCauchyTrace_hasExterior |
| NativeGammaMaterialCameraLift | materialCamera_natDegree; materialCamera_top_coefficient |
| NativeGammaMaterialPolynomialProvenance | materialCameraPolynomial_C2; materialNaturalCameraPolynomial |
| NativeGammaMaterialDecoder | materialCameraLift_maxDegreeMinor; materialCameraDecode_lift |
| NativeGammaMaterialTransport | gammaMaterialTransport_roundtrip; gammaMaterialTransport_injective |
| NativeGammaMaterialMetric | gammaMaterialTransport_metricLedger; materialCameraGram_one_two_three |
| NativeGammaMaterialGraphDefect | gammaMaterialGraphDefect_entirePair; gammaMaterialGraphDefect_faithful |
| NativeGammaMaterialCrossings | nativeGammaCameraWholePair_sum; nativeGammaCameraDefects_faithful |
| NativeGammaMaterialHeadTailLedger | nativeGammaMismatch_materialHeadTailLedger; nativeGammaWholePair_camera_fourHeadTails |
| NativeGammaMismatchLedger | nativeGammaMismatch_materialDefectLedger; nativeGammaMismatch_proposedLedgerDifference |
| NativeGammaOrientationObstruction | nativeGammaMismatch_proposedLedger_fails_at_witness |
| NativeGammaObservableTransportCapstone | nativeGammaObservableTransport_capstone; gammaMaterialFirstPort_correctedGreen |

## Validacao efetiva

Registro publico: `audit/gamma-cauchy-transport-registry.json`, com
208 declaracoes em 20 modulos pequenos, cada um com Audit correspondente.
Cada Audit contem #check, #print axioms e o guard transitivo dos tipos e
corpos. Apenas propext, Classical.choice e Quot.sound sao permitidos.

Procedimento reproduzivel:

```bash
PATH=/home/thlinux/.elan/bin:$PATH bash scripts/audit_gamma_cauchy_transport.sh
```

O procedimento compila cada Audit com --wfail, executa cada auditoria
diretamente, valida o registro e a auditoria estatica, faz o build raiz
--wfail e executa scripts/audit.sh. Os logs efetivos, ambiente, base,
estado local e SHA256 das fontes ficam em
`.lake/gamma-cauchy-transport-audit/`.

Resultado da rodada integral: PASS, executado no host llm, codigo de saida 0.
Os 20 builds individuais dos Audits com --wfail e as 20 execucoes diretas
passaram. A maior clausura de dependencias auditada foi 7134 constantes,
no capstone. As 208 declaracoes passam o guard dos tipos e corpos, com
somente os tres fundamentos permitidos. Nao ha sorry, sorryAx, novos
axiomas ou hipoteses que sejam a conclusao.

O registro publico, a auditoria estatica, o build raiz --wfail
(10150 jobs, incluindo dependencias reaproveitadas) e scripts/audit.sh
passaram. Nenhuma falha herdada foi encontrada nessa rodada integral.
As mensagens informativas antigas de ring nao sao warnings nem falhas.
git diff --check e a verificacao dos SHA256 completam o registro.
CI externa e registrada separadamente; jobs que nao iniciam nao substituem
qualquer destes comandos Lean efetivamente executados.

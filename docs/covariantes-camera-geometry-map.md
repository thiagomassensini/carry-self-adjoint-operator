# Covariantes: transporte, platôs e bordo das câmeras

Data: 2026-09-05.
Fonte da pesquisa: servidor `llm:/home/thlinux/covariantes`.
Base Lean conferida: `0048cde62e9a2a4dfbd7d41c8a0be8be9df9b379`, descendente da base solicitada `225a85d9e8e3e0a3b659c5b6ad821458770b3195`.
Este documento acrescenta um mapa de fontes e uma reprodução dirigida. Não constrói operador, momentos, Gamma ou Jacobi.

## O que a pesquisa acrescenta

A contribuição mais direta é uma comparação **covariante**: transportar a fibra antes de calcular a variação da corrente. Isso separa a mudança do estado da mudança de suas coordenadas de câmera. A pesquisa também guarda exemplos em que a leitura escalar coincide, mas a informação vetorial complementar continua necessária para o Green.

Isso dá conteúdo geométrico ao resultado anterior sobre platôs: câmeras fixas podem chegar à mesma leitura normalizada sem que seus vetores coincidam. A visita não encontrou uma identificação tipada entre o levantamento por valuações destas notas e a fonte Gamma C3 atual.

A pasta contém 245 arquivos Markdown fora dos caches e nenhum arquivo Lean. O README é uma cópia byte a byte de `TEORIA_GEOMETRICA_DO_CARRY_E_OPERADOR_ORTOGONAL_MULTIBASE.md`; a síntese é datada de julho de 2026. Foram examinados trechos e notas dirigidos a transporte, coerência, sementes, células completas e trace. Não foi auditado integralmente todo o acervo. Os rótulos PASS/STOP nas notas descrevem rodadas de pesquisa e testes; não substituem declarações Lean.

## 1. A identidade de transporte que merece ser guardada

Fonte: `README.md` §§25–27, linhas 1433–1577; `script/c2_covariant_multibase_connection.py:108–151,615–695`.

Para $n\ge2$, a fibra prima da nota é

$$
a_p(n)=\sqrt{\frac{v_p(n)\log p}{\log n}},
\qquad \sum_p |a_p(n)|^2=1.
$$

A soma vem de $\sum_p v_p(n)\log p=\log n$. Aqui $a(n)$ é um vetor de pesos de valuação, **não** a resposta escalar $-F'/2F$. A fonte $n=1$ requer o seed separado; esta fórmula não o define.

Para uma seção coerente $y(n)=a(n)f(n)$, a diferença ordinária satisfaz

$$
y(v)-y(u)
=a(v)\bigl(f(v)-f(u)\bigr)
+\underbrace{\bigl(a(v)-a(u)\bigr)f(u)}_{\text{variação da fibra}}.
$$

Com $T_{u\to v}=|a(v)\rangle\langle a(u)|$ e
$\nabla_Ty(u,v)=y(v)-T_{u\to v}y(u)$, obtemos, por substituição,

$$
\nabla_T(Vf)(u,v)=a(v)\,df(u,v),
\qquad
\|\nabla_T(Vf)(u,v)\|^2=|df(u,v)|^2.
$$

A síntese por $\langle a(v),\cdot\rangle$ recupera $df$. Esta é uma dedução algébrica a partir da normalização das fibras, conferida também no código da pesquisa. Não foi acrescentado um teorema Lean nesta rodada.

**Escopo do transporte.** $T$ seleciona a linha coerente. Para preservar estados arbitrários e seu complemento, as notas usam uma extensão unitária $Q_{u\to v}$ com $Q_{u\to v}a(u)=a(v)$. Essa condição não determina sozinha a ação no complemento.

`C2_COVARIANT_HIDDEN_KERNEL_GAUGE_AUDIT.md` registra duas extensões que concordam na linha coerente, mas têm curvaturas diferentes no setor oculto. `C2_PRIME_FILTRATION_UNITARY_COCYCLE.md` descreve a ativação de uma banda prima mais a coordenada futura. `C2_DYNAMIC_CP_CONNECTION_CURVATURE.md` esclarece que uma coordenada futura escalar não recupera todas as futuras coordenadas CP/Haar. Estes são guias para preservar o complemento, não identidades com o Gamma C3 atual.

**Domínio.** A seção $n^{-s}$ não pertence ao $\ell^2$ de contagem em $\Re s=1/2$. A identidade covariante pode ser estudada primeiro em cortes finitos ou seções pontuais, conservando o seed, e depois no espaço das correntes. Não se pode inseri-la diretamente em um parâmetro Lean do tipo `GreenFrame.Concrete.State`, que é $\ell^2(\mathbb N_{>0},\mathbb C)$, sem provar pertinência. Isso não impede o estudo do gradiente no seu domínio próprio.

## 2. Três realizações que não devem receber o mesmo nome

| Objeto | Tipos / índices efetivos | Correspondência verificada |
|---|---|---|
| Levantamento da nota | Valores $f(n)$ para fibras $(n,p)$, pesos $v_p(n)\log p/\log n$ | Fórmula covariante acima; laboratório Python. |
| Atlas elementar GreenFrame | `State →ₗᵢ[ℂ] ElementaryAtlasSpace`, com seed e partição admissível | `elementaryAtlasLinearIsometry` e especialização `canonicalCarryElementaryAtlas` já existem. A partição canônica usa pesos de log-profundidade sobre bases; não foi identificada aqui com a partição prima da nota. |
| CameraHilbert/Weyl | Completação do Gram periódico das câmeras; realização em $L^2((0,\infty),K_0)$ | `naimarkCameraVector` e o centramento `centeredCameraIsometry` preservam o mesmo Gram de câmeras. Não são, por definição, a fibra $(n,p)$ da primeira linha. |

O source C3 atual tem outra entrada bem delimitada:
`canonicalC3SixCameraSourceMap : FiniteC3GreenPortCarrier 3 → RealifiedCameraComplexification`.
Ele embala as duas pernas completas, cada uma com três células complexas, nas câmeras $2,\ldots,7$, mantendo as duas quadraturas. Não é definido como o vetor de seis resultantes da nota nem como o levantamento por valuações.

## 3. Coerência, leitura escalar e o palpite dos platôs

`README.md` §15, linha 852, distingue:

- $P_{\rm coh}$: os registros provêm de um mesmo estado aritmético;
- $P_{\rm syn}$: a componente visível a um funcional escalar.

São perguntas diferentes. A coincidência das leituras normalizadas não estabelece igualdade dos registros.

No Lean atual, a distinção já tem resultados concretos, todos reutilizáveis:

| Declaração existente | O que afirma |
|---|---|
| `finiteCamera_normalizedPhysicalCutoff_pairwise_tendsto` | Para duas câmeras fixas e altura real fixa, a diferença dos readouts divididos pelos respectivos fatores tende a zero, com centros completos no mesmo cutoff físico. |
| `completeCameraCenterCount_initialPlateau` | Antes do primeiro centro completo, a contagem de centros é zero. |
| `finiteCamera_three_five_unitSeparation_tendsto` | Na covariância completa de coeficientes, a separação quadrática unitária entre as câmeras 3 e 5 tende a $2$, para parâmetro de resolvente não real. |
| `normalizedCompletedNativeCameraCharacteristic_eq` | Com head + cauda exata e o fator comum de completion, cada câmera normalizada já é a mesma função em todo cutoff. |
| `centeredCameraIsometry_readout` | Transportar estado **e observador** pelo centramento preserva seu produto interno. |
| `sixCamera_return_variance_polarization` | Os dois canais $A$ e $\sqrt V$, juntos, preservam todos os produtos cruzados. |

A variável de altura das duas primeiras linhas não foi identificada com o parâmetro de resolvente da terceira. Também não foi provada uniformidade quando a base cresce com o cutoff.

O material reforça a investigação dos platôs em três níveis: massa visível por fibra, leitura escalar calibrada e geometria vetorial completa. Cada nível exige sua própria comparação.

## 4. Duas obstruções antigas que as próprias notas corrigem

### Endpoint omitido

Fontes: `C2_GREEN_RECOVERED_RETURN_CROSSWALK_REPORT.md`;
`script/c2_green_recovered_return_crosswalk.py:316,388`.

Na convenção eta/block desse laboratório,

$$
\Phi_{\eta,N}^{\rm atual}(s)-\Gamma_{(1,2),N}^{\rm antigo}(s)
=(2N+1)^{-s}-(2N+2)^{-s}.
$$

O certificado racional de $n=1$ muda ao reinserir esse endpoint: $wS_{\rm antigo}=(2,2,0,0)$ e $wS_{\rm endpoint}=(-2,-2,0,0)$, enquanto $wS_\eta=0$. O teste exato com `Fraction` e o teste numérico do endpoint passaram novamente.

Isso corrige aquele certificado; não identifica os antigos $\Gamma,\Phi_\eta$ com os tipos do Gamma C3.

### Bloco completo, centros coarse e duas pernas

Fontes: `C2_GREEN_ENERGY_OPERATOR_CORRECTION_ADDENDUM.md`;
`C2_GREEN_FULL_EVEN_INTERTWINER_CORRECTION.md`;
`script/c2_green_full_even_hodge_endpoint.py:212`.

O operador do ledger de quatro cantos lê $\sqrt2[u(2n)+u(2n+1)]$. Usar apenas $\sqrt2u(2n)$ muda o endpoint. Com todos os centros pares, incluindo a camada coarse $k=1$, a nota recupera

$$
C_{\rm ev}f(j)-2^{-1/2}R_{\rm ev}^{\rm br}f(j)=\sqrt2 f(2j).
$$

O antigo witness $\delta_5$ deixa de refutar esse intertwiner completo. A reauditoria simbólica passou. Isto apoia a insistência em centros e pernas completos; não autoriza transplantar uma conclusão de porta eta/block para a célula C3 sem mapa.

## 5. A cauda tem uma descrição geométrica própria

Fontes: `C2_UNIT_MASS_TAIL_BOUNDARY_REPORT.md`;
`script/c2_green_unit_mass_tail_boundary.py:534,556`;
`tests/test_c2_green_unit_mass_tail_boundary.py:29,99,109`.

Para o núcleo ímpar $m$, a nota conserva os dois limites de profundidade das pernas $2^km\pm1$. A massa visível $a_X(m)$ e a futura $\rho_X(m)$ somam $1$. Nos núcleos ativos $m<2M$,

$$
\rho_{8M}(m)=\frac{\rho_{4M}(m)}2,
\qquad
a_{8M}(m)-a_{4M}(m)=\frac{\rho_{4M}(m)}2.
$$

As fibras dormentes não são incluídas nessa lei. O caso $X=12,m=3$ distingue literalmente a perna $11$ já visível da perna $13$ ainda ausente.

A shell de massa $4M\to8M$ reproduz o bordo de quatro cantos com cutoff Green **$N=8M-1$**. Os testes comparam coeficientes racionais, preservando os pares não reduzidos e seu gcd. O cutoff $8M$ não dá a mesma igualdade. É uma ponte concreta massa–bordo no laboratório C2, ainda sem identificação operatorial com o retorno Gamma usado no autoadjunto.

## 6. Valor e fluxo pedem um transporte conjunto

Fontes: `C2_GREEN_PORT_TRACE_DUALITY_ADDENDUM.md`;
`C2_GREEN_PORT_TRACE_RENORMALIZATION_REPORT.md`;
`C2_GREEN_SCALE_NAIMARK_PORT.md`.

A nota preserva o pareamento por transporte contragrediente:

$$
\Gamma^- = T^{-1}\Gamma,\qquad
\Psi^+=T\Psi,\qquad
\langle\Gamma^-,\Psi^+\rangle=\langle\Gamma,\Psi\rangle.
$$

A identidade é imediata no núcleo finito para $T$ positivo invertível. No infinito, $T=m^2$ é não limitado: a nota define espaços duais para dar sentido ao pareamento. Convergência do valor transformado, isoladamente, não prova a convergência do fluxo. Não foi assumido aqui nenhum bound ausente.

O paralelo formal já disponível no autoadjunto é a preservação do readout ao transportar estado e observador pelo **mesmo** mapa isométrico, e a decomposição Green com a componente cega conservada. São mecanismos a comparar, não uma igualdade automática entre os espaços.

## 7. Peças Lean localizadas e conferidas

Os caminhos abaixo são relativos ao checkout atual. Os pins foram mantidos.

- `CarrySelfAdjointOperator/CenteredCameraCutoffConvergence.lean`: centramento, Gram cruzado, extensão isométrica, platôs, convergência escalar e separação das câmeras.
- `CarrySelfAdjointOperator/CameraReturnVarianceEnergyBalance.lean`: partição retorno/variância, polarização e dual geométrico da leitura de valor.
- `CarrySelfAdjointOperator/FiniteEnrichedCameraState.lean`: `finiteCanonicalEnrichedCamera_parseval`, `finiteCanonicalEnrichedCamera_reconstruct` e `finiteCanonicalEnrichedCamera_greenDecomposition`. A hipótese é positividade do Gram **finito das linhas da câmera**, não do Hankel nativo.
- `CarrySelfAdjointOperator/CanonicalC3SixCameraSource.lean`: empacotamento fiel; a injetividade não é uma prova de isometria da métrica original do porto.
- `CarrySelfAdjointOperator/C3ReturnCompletedTraceChannels.lean:209`: `c3CanonicalRawValue_eq_return_add_cameraSeven_tail`, com os termos que uma leitura só do retorno omite:
  $$
  \mathrm{rawValue}(z)
  =1-\frac3{\sqrt{278}}\mathrm{returnReadout}(\mathrm{source}(z))
   +\mathrm{positiveDirichletGradient}(s(z),2)
   +\mathrm{realCpBracketCutoffTail}(3,1,s(z)).
  $$
  A hipótese é $s(z)$ na faixa crítica aberta. A expressão é a leitura raw correspondente, sem renomeá-la como o valor completado $F$.
- `CarrySelfAdjointOperator/CompletedNativeCameraUniversality.lean`: igualdade exata das características normalizadas com head + cauda e completion.
- `.lake/packages/GreenFrame/GreenFrame/Concrete/Analysis/ElementaryAtlasIsometry.lean`: atlas elementar isométrico já existente, com seed. Pin GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- `.lake/packages/CPFormal/CPFormal/Carry/CpMultibaseCameraAtlasHilbert.lean`: `isCompl_cameraVertical_horizontal` e `logEval_not_injective`. Apesar do nome do arquivo, este módulo fornece um espaço livre algébrico de suporte finito, não sua completação Hilbert. Pin CPFormal: `65d50f6db1208708e109982ba97e1d51d3039956`.
- `.lake/packages/NativeCarrySpectralWeyl/NativeCarrySpectralWeyl/Infinite/Naimark.lean`: realização de todo o Gram periódico por funções indicadoras. Pin: `298d83c9351e308a5213b9f5ac32e44087f98a9f`.

A busca dirigida por conexão covariante/Householder nas fontes CPFormal e GreenFrame consumidas não localizou a identidade $\nabla_QV=V_Ed$ dessa nota como ponte integrada. Isso delimita esta busca; não prova ausência em todos os repositórios e branches.

## 8. Próxima experiência geométrica, sem impor o kernel final

1. Usar o transporte covariante nas correntes e comparar o termo de mudança de fibra antes e depois, mantendo seed e ledger completo. O diagnóstico finito abaixo já reproduz o mecanismo.
2. Comparar os observadores de valor e fluxo sob esses transportes. No CameraHilbert, reutilizar `centeredCameraIsometry_readout` e o dual de valor já calculado, em vez de refazer uma métrica.
3. Se surgir uma ponte entre a fibra de valuações e o CameraHilbert, exigir primeiro a fórmula do mapa e de seus produtos cruzados, depois a compatibilidade de trace. Os dois tipos atualmente não estão identificados. O fechamento Gamma–Wronskiano não foi obtido nesta visita.

Esse roteiro não assume que o levantamento da nota seja o source completo. Também não remove a câmera 7, a cauda ou o canal complementar para obter uma coincidência escalar.

## 9. Verificação desta rodada

**Laboratório existente:** 174 testes passaram em cinco módulos, em 30,07 s. Cobrem endpoint, blocos, transporte contragrediente, células completas/coarse e unit mass–bordo. Há testes algébricos exatos, testes de tolerância numérica e testes de integridade de artefatos; o total não significa 174 teoremas analíticos.

**Reprodução covariante adicional:** foi executada a função existente `exact_connection_audit`, sem modificar seu construtor, com câmeras $2,3,5,7,11,13$, campos complexos pseudoaleatórios de seed 20260905 e cortes de 8, 64 e 256 centros por câmera. No maior corte: 9.216 arestas, erro máximo de entrelaçamento $5,02\cdot10^{-16}$, erro máximo de recuperação de uma corrente $8,01\cdot10^{-16}$ e erro da síntese total $4,27\cdot10^{-14}$.

A energia do termo de variação da fibra dividida pela energia covariante foi aproximadamente $0,868$, $0,951$ e $0,950$ nesses três campos finitos. Isso mostra que o termo pode ser material; não prova seu limite para uma seção nativa ou um comportamento universal em altura.

**Integridade:** os 1.404 arquivos de entrada, excluindo caches Python/pytest, foram conferidos por SHA-256 antes e depois dos testes. Nenhum mudou. Os 54 witnesses históricos foram reutilizados e não reotimizados. Não foram executados os programas principais que regravam relatórios.

**Lean:** os dois alvos auxiliares de atlas foram compilados com sucesso no pin atual; 11 declarações existentes foram consultadas com `#check` e `#print axioms`. Todas as 11 consultas retornaram somente `propext`, `Classical.choice` e `Quot.sound`, sem `sorryAx`. Não foi criado teorema novo. O workflow integral de 14 estágios não foi repetido nesta rodada documental.

Artefatos: [log dos testes](../research/covariantes-camera-audit-2026-09-05/pytest.log), [proveniência e hashes](../research/covariantes-camera-audit-2026-09-05/provenance.json), [diagnóstico covariante](../research/covariantes-camera-audit-2026-09-05/covariant-diagnostics.json), [consultas Lean](../research/covariantes-camera-audit-2026-09-05/existing-lean-declarations.log) e [comandos das consultas](../research/covariantes-camera-audit-2026-09-05/ExistingDeclarations.lean.txt), [build dos atlas](../research/covariantes-camera-audit-2026-09-05/lean-target-build.log).

Para repetir os testes, no servidor, a partir de `/home/thlinux/covariantes`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 \
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
/home/thlinux/miniforge3/bin/python -m pytest -q -p no:cacheprovider \
  tests/test_c2_green_recovered_return_crosswalk.py \
  tests/test_c2_green_block_operator_intertwiner.py \
  tests/test_c2_green_port_trace_renormalization.py \
  tests/test_c2_green_full_even_hodge_endpoint.py \
  tests/test_c2_green_unit_mass_tail_boundary.py
~~~

O roteiro do diagnóstico adicional está em [reproduce-covariant.py](../research/covariantes-camera-audit-2026-09-05/reproduce-covariant.py). Ele chama o script original e grava somente em um diretório temporário ou no destino explicitamente informado.

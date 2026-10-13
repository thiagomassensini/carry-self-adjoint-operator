# Resolvente misto, exteriores e balanço dos cruzamentos

Data: 13/10/2026. Repositório: `thiagomassensini/carry-self-adjoint-operator`.
Base efetiva: `ce860946bd0cfcac639fb465eb69667e1d9b8367`, após PR #80.

## Proveniência e escopo

A genealogia foi consultada primeiro no README de `carry-raiz`, revisão
`2b998993a7b911729989f2ef76cdd02448c9fd77`, pela API do repositório. O anexo
`Estudo_Cores_Resolventes_e_Transporte_2026-10-13(1).md` foi lido integralmente,
incluindo código, resultados e fontes; SHA-256
`83fff3dda60212a3c4172c1e3b5c9cab9e59414d9d061f1f8183b21ef91142b3`.
Seus testes racionais e decimais não são premissas das provas abaixo.

O HEAD e `origin/main` coincidiam com a base. A única PR aberta era #62,
sobre outra obrigação de momentos. Os dois arquivos C2 locais e as três
worktrees preexistentes foram preservados. A implementação usa a worktree
própria `/home/thlinux/carry-mixed-resolvent`, branch
`agent/mixed-resolvent-three-sectors`, com cache de build copiado sem hardlinks.

Os pins não foram atualizados:

| Dependência | Commit |
|---|---|
| NativeCarrySpectralWeyl | `298d83c9351e308a5213b9f5ac32e44087f98a9f` |
| NativeCarryC3Crosswalk | `150cfc7fb08da96bf8117f15869cc2b819d593c2` |
| CPFormal | `65d50f6db1208708e109982ba97e1d51d3039956` |

Não há novo carrier, nova métrica, ajuste de constante ou nova fonte. O
relógio permanece literalmente `Y = 1 + log x`. O Cauchy é a compressão de
`(z-Y)⁻¹`, anti-Herglotz no semiplano superior. A primeira entrada do produto
interno é antilinear. A fonte nativa não vestida continua distinta de sua
completação arquimediana.

## A. Modo misto e dois parâmetros

Escreva `E = nativeSixCameraSynthesis`, `G = nativeSixCameraGram`,
`w = (-6,-3,2,0,3,0)` e `f = Ew`. Os labels são `(2,3,4,5,6,7)`;
C6 é `4 : Fin 6`, não a sexta posição da lista.

`nativeMixedVector_eq_original` identifica `f` com a complexificação literal
de `sixCameraReturnVector`. A dualidade e a norma são

\[
\langle f,Ec\rangle=(278/3)c_4,\qquad \|f\|^2=278.
\]

O vetor `nativeMixedUnitVector` é `ξ = f/√278`, com norma um. Os adaptadores
`nativeMixedCoefficients` e `nativeMixedComplement` satisfazem

\[
c_*=(c_4/3)w,\quad c_\perp=c-c_*,\quad(c_\perp)_4=0,
\quad c_*+c_\perp=c.
\]

`nativeMixedCoefficients_pack` e `nativeMixedComplement_pack` identificam
esses vetores com o packing de `sixCameraMixedReturnPortPart` e seu
complemento. As sínteses canônicas são exatamente
`canonicalC3ReturnSourcePart` e `canonicalC3ReturnSourceRemainder`.

`nativeCameraFiber` é o indicador literal do intervalo original vezes o
vetor Kolmogorov original. A matriz periódica auxiliar está provadamente
igual a `periodicMeanKernel`, usando o Gram original e os níveis positivos.
Não é uma realização alternativa. Os teoremas pontuais dão, inclusive nos
endpoints dos indicadores,

\[
\|F_*(x)\|^2=\rho(x)=
\begin{cases}32&0<x\le3,\\50&3<x\le4,\\66&4<x\le6,\\0&\text{caso contrário},\end{cases}
\quad
\langle F_*(x),F_j(x)\rangle=
\begin{cases}\rho(x)/3&j=4,\\0&j\ne4.\end{cases}
\]

A representante da síntese Naimark é identificada quase em toda parte
por `nativeRealSixNaimarkSynthesis_coeFn`. Para quaisquer dois multiplicadores
reais limitados originais, o produto integrado entre o modo misto e uma
síntese com C6 nula é zero. A prova Gamma aplica isso às oito combinações
das partes reais/imaginárias dos dois resolventes e das duas quadraturas
da fonte. Portanto

\[
\langle\Gamma_z(Ec_*),\Gamma_\omega(Ed_\perp)\rangle=
\langle\Gamma_z(Ec_\perp),\Gamma_\omega(Ed_*)\rangle=0
\]

para entradas independentes e apenas `z.im ≠ 0`, `ω.im ≠ 0`.
Não há divisão por `ω-conj z`, exclusão da colisão, continuidade postulada
ou hipótese de ortogonalidade. O roundtrip Gamma já existente é reutilizado;
o Gram canônico tem agora os dois cruzamentos específicos avaliados como
zero. O complemento não é removido: suas não nulidades na faixa Genuine
continuam certificadas por `canonicalC3ReturnSourceRemainder_ne_zero` e
`canonicalC3ReturnGammaRemainder_energy_pos`.

A resposta é definida geometricamente pelas mesmas integrais nativas:

\[
r_*(z)=\frac{-9I_3(z)-8I_4(z)+33I_6(z)}{139}.
\]

`nativeMixedCauchy_camera_readout` deriva suas seis leituras das entradas
integrais originais. Seguem

\[
\alpha(C_zf)=r_*(z)w,\quad P(C_zf)=r_*(z)f,
\quad\langle\xi,C_z\xi\rangle=r_*(z).
\]

Isso é compressão, não uma igualdade `C_zf = r_*f` no Hilbert inteiro.
O kernel principal é definido pelos vetores completos,

\[
k_*(z,\omega)=\langle\Gamma_z\xi,\Gamma_\omega\xi\rangle,
\qquad(\omega-\overline z)k_*=
\overline{r_*(z)}-r_*(\omega).
\]

A identidade é sem divisão, também na colisão. Não foi necessário criar
uma nova representação integral desse kernel vetorial.

## B. Três setores do resolvente inteiro

`nativeComplexNaimarkPort` e `nativeComplexNaimarkAdjoint` são adaptadores
lineares complexos da aplicação e do adjunto reais originais. Sua igualdade
literal, isometria, identidade de adjunto Hilbert e leitura Gamma são provadas:

\[
\langle Vu,f\rangle=\langle u,V^*f\rangle,
\quad\|Vu\|=\|u\|,\quad V^*\Gamma_z u=C_zu.
\]

`nativeComplexGamma_eq_original` identifica o adaptador complexo Gamma
com `carryGammaComplexState`, sem mudar suas quadraturas ou norma.
Defina o vetor de escape global

\[
\varepsilon_z(u)=\Gamma_z u-V(C_zu).
\]

Seu roundtrip e sua ortogonalidade a todo `Vv`, em ambas as ordens, são
provados para fontes arbitrárias. O vetor é identificado com
`canonicalCompletedC3AmbientPortEscape` e com a complexificação de
`globalNaimarkCameraEscape`, portanto com o escape original `I-VV*`.

Com `d_z(c)=α(C_zEc)` e `h_z(c)=Q(C_zEc)`, o endpoint vetorial é

\[
\boxed{\Gamma_zEc=VE d_z(c)+Vh_z(c)+\varepsilon_z(Ec).}
\]

Os seis cruzamentos entre esses três setores são avaliados como zero para
fontes e parâmetros independentes. Consequentemente

\[
\langle\Gamma_zEc,\Gamma_\omega Ed\rangle=
d_z(c)^*Gd_\omega(d)+\langle h_z(c),h_\omega(d)\rangle+
\langle\varepsilon_z(Ec),\varepsilon_\omega(Ed)\rangle.
\]

A projeção das seis câmeras na dilatação é construída, no mesmo carrier,
como `V P V*`. Seu range é exatamente `Ran(VE)`, é idempotente e seu
complemento é ortogonal a esse range. Isso fornece a versão complexa
equivalente da decomposição halo/escape, com identificação explícita dos
mapas originais:

\[
(I-VPV^*)\Gamma_zEc=VQ(C_zEc)+\varepsilon_z(Ec).
\]

Seu pairing é a soma dos pairings de halo e escape global, sem termos
mistos. O halo nativo, o escape global e a cauda Laguerre são objetos
diferentes. Em particular `Qa_z=0` não elimina `Q(C_za_z)`.

As matrizes são definidas pelas câmeras originais, não por coeficientes
brutos silenciosamente equipados com uma métrica euclidiana:

\[
\mathcal C(z)_{ij}=\langle e_i,C_ze_j\rangle,\quad
\mathcal H(z,\omega)_{ij}=\langle QC_ze_i,QC_\omega e_j\rangle,\quad
\mathcal E(z,\omega)_{ij}=\langle\varepsilon_z(e_i),\varepsilon_\omega(e_j)\rangle.
\]

O adjunto hermitiano é explícito no teorema
`nativeGammaResolvent_matrixIdentity`:

\[
\boxed{\mathcal C(z)^*-\mathcal C(\omega)=
(\omega-\overline z)
[\mathcal C(z)^*G^{-1}\mathcal C(\omega)+\mathcal H(z,\omega)+\mathcal E(z,\omega)].}
\]

Vale para todo par fora do eixo real. O corolário dividido exige
`ω-conj z ≠ 0`. Para `z.im > 0`, com
`nativeGammaHermitianImaginary A = (2i)⁻¹(A-A*)`,

\[
-\operatorname{Im}_H\mathcal C(z)/\operatorname{Im}z=
\mathcal C(z)^*G^{-1}\mathcal C(z)+\mathcal H(z,z)+\mathcal E(z,z).
\]

Todas as formas quadráticas dos dois Grams exteriores são normas
quadradas reais não negativas, como provado em
`nativeGammaHaloMatrix_quadratic`, `nativeGammaEscapeMatrix_quadratic` e
`nativeGammaExteriorGrams_nonnegative`. Isso não afirma positividade da
forma quiral assinada.

## C. Balanço material, sem apagar cruzamentos

`nativeGammaSourcePair z hz c = (Ec,C_zEc)` produz ambos os segundos ports
pelo mesmo Cauchy original. A decomposição mista/complemento e sua soma
canônica são identidades do par inteiro. Os dois lemas `*_literal`
identificam os pares com os source part/remainder originais, inclusive
seus segundos componentes Cauchy.

O transporte ambiente usa somente o lift material original e as
coordenadas nativas fixadas:

\[
p=(a,b)\longmapsto
\operatorname{twoPortSynthesis}(J_C\alpha a,J_C\alpha b).
\]

`nativeGammaMaterialAmbientPair_add` e
`nativeGammaMaterialAmbientDefect_add` conservam a soma das duas pernas
e a soma dos defeitos `s-θv`. O produtor não consulta `θ` para definir `s`.
O lift permanece o das seis finiteStencil originais: C2 moderna com
centros `4m`, seeds e todos os raios; não é a carta FULL-EVEN de centros `2m`.

Pela identidade Green nativa e a ortogonalidade Gamma demonstrada,
os dois cruzamentos Green desses pares são zero. As fontes estão em `Ran E`,
logo o setor exterior da forma é zero, mas os exteriores dos segundos
componentes permanecem no transporte e nos Grams.

Com `Δ_C=G-J_C*H_NJ_C`, a consequência material é exatamente

\[
\boxed{g_H(p_*(z),p_\perp(\omega))+\mathcal M_C(p_*(z),p_\perp(\omega))=0,}
\]

e a mesma identidade com as duas entradas trocadas de setor.
Os sinais são os de `gammaPhysicalGreenScale_form` e do ledger nativo
do PR #80. Não se afirma que `g_H` ou `M_C` se anulem individualmente.
Os enunciados valem para todo cutoff material, inclusive `C=0`.
`C≥1` aparece somente nos roundtrips que usam o decoder material injetivo.

`nativeGammaMaterialAmbientGreenHeadTail` mantém os dois produtos físicos
com cabeça mais cauda. Para todo `R`, ambos os balanços continuam exatos.
O capstone reutiliza os probes fiéis do segundo port. As expansões
independentes em 36 pares de câmeras e quatro setores são as já
certificadas em `nativeGammaWholePair_camera_fourHeadTails` e
`nativeGammaCamera_fourHeadTails`; foram mantidas e auditadas, não
substituídas por uma cabeça curta.

## D. C9, variância e mismatch existente

O C9 original mede exatamente a mesma coordenada mista:

\[
\langle q_9,C_zEc\rangle=\beta_9(z)c_4
=\frac{3\beta_9(z)}{278}\langle f,Ec\rangle.
\]

Seu probe do segundo port complementar é zero; seu probe do segundo port
misto coincide com o do par inteiro. Isso não torna C9 fiel a todo o
complemento ou a todo o exterior.

De sua ortogonalidade às seis câmeras e de Cauchy-Schwarz, resulta

\[
\boxed{\|\beta_9(z)\|^2\|c_4\|^2\le
(9012/139)\|QC_zEc\|^2.}
\]

O corolário dividido prova a positividade da constante. A aplicação
canônica usa `c_4=positiveDirichletGradient(s,1)=3^{-s}-2^{-s}`.
Em `z₀=4+i/8`, a cota inferior é estritamente positiva pela testemunha
analítica anterior de `β_9(z₀)≠0` e pelos módulos distintos da coordenada
original. Não foram avaliados numericamente `F`, zeta ou o quociente quiral.

A identidade Ward do modo misto e o Gram de três setores dão

\[
\boxed{\delta_*(z)=-\frac{\operatorname{Im}r_*(z)}{\operatorname{Im}z}
-|r_*(z)|^2=\|QC_z\xi\|^2+\|\varepsilon_z(\xi)\|^2\ge0.}
\]

Para todo parâmetro fora do eixo real,

\[
\delta_*(z)\ge\frac{9|\beta_9(z)|^2}{278(9012/139)},
\qquad\delta_*(4+i/8)>0.
\]

Não se postulou positividade estrita em todo o domínio. Essa extensão
analítica, discutida no anexo pela medida contínua, não foi necessária
para a identidade exata nem para a positividade no ponto original.

Com `b_1(z)=nativeCanonicalGammaCoefficients z 4`, a parcela mista é

\[
\langle m_z,m_\omega\rangle=
\frac{278}{9}\overline{b_1(z)}b_1(\omega)k_*(z,\omega).
\]

Na faixa Genuine, usando exatamente as hipóteses e a ordem do módulo
original, `nativeGammaMismatch_mixedComplementReduction` prova

\[
\boxed{\operatorname{Mismatch}_{nat}(z,\omega)=
\frac{278}{9}\overline{b_1(z)}b_1(\omega)
(\overline{r_*(z)}-r_*(\omega))+
(\omega-\overline z)\langle r_z,r_\omega\rangle-
\mathscr W_N(\omega,z).}
\]

O lado esquerdo é o já existente
`canonicalCompletedC3NativeSourceLocusProjectionMismatch`. O Wronskiano
é literalmente `completedGreenWronskian nativeHeightScalar
nativeHeightScalarBoundaryCompanion ω z`, não o da característica vestida.
A igualdade é sem divisão e inclui a colisão.

`nativeGammaMismatch_mixedReduction_materialLedger` identifica essa mesma
expressão com o ledger corrigido anterior:

\[
-\mathcal M-\mathcal A-v^*H\eta'+\eta^*Hv'-2\mathscr N_{scal}.
\]

Não foi mudado seu sinal, suprimido o defeito de referência ou assumida
a anulação do mismatch.

## Capstones e hipóteses

`nativeGammaMixedTransport_capstone` reúne a reconstrução dos dois pares
nativos originais, a soma material de duas pernas, a fidelidade dos probes,
os dois balanços cabeça + cauda e o roundtrip halo/escape global.
Exige apenas `C≥1` para reconstrução e os dois parâmetros fora do eixo real.
Os balanços individuais não exigem `C≥1`.

`nativeGammaMixedResolvent_capstone` reúne o vetor Gamma original em três
setores, ambos os cruzamentos nulos, a redução do mismatch nomeado,
a variância exata, sua positividade no ponto testemunha e o exterior
canônico original não nulo. A faixa Genuine só é necessária para a
identificação do mismatch com o Wronskiano não vestido.

Não há hipótese de não nulidade de `F`, de coordenada Hermite-Biehler ou
de denominadores radiais nessas novas conclusões: elas não utilizam essa
identificação radial completada. Onde a infraestrutura anterior faz tal
identificação, suas hipóteses permanecem nas declarações anteriores.

## Auditoria requisito por requisito

N = prova nova; C = corolário novo por composição; R = prova anterior reutilizada.
Todos os arquivos abaixo pertencem a `CarrySelfAdjointOperator/`.

| Item | Arquivo e declaração | Status |
|---|---|---|
| A1: vetor original, dualidade, norma | `NativeGammaMixedSource`: `nativeMixedVector_eq_original`, `nativeMixedVector_inner_synthesis`, `nativeMixedVector_norm_sq` | N/C |
| A1: splitting C6 e packing original | Mesmo: `nativeMixedCoefficients_roundtrip`, `nativeMixedComplement_cameraSix`, `nativeMixedCoefficients_pack`, `nativeMixedComplement_pack` | N |
| A1: sources canônicos existentes | Mesmo: `nativeCanonicalMixedSource_eq_original`, `nativeCanonicalComplementSource_eq_original` | C |
| A2: matriz periódica original, exceção C2 | `NativeGammaMixedProfiles`: `nativeSixPeriodicMean_eq_original` | C |
| A2: perfis pontuais e densidade | Mesmo: `nativeCameraFiber_inner`, `nativeMixedFiber_camera_inner`, `nativeMixedFiber_norm_sq` | N |
| A2: representantes Lp originais | `NativeGammaMixedMultiplierOrthogonality`: `nativeRealSixNaimarkSynthesis_coeFn`, `nativeRealSixNaimarkSynthesis_mixed_coeFn` | N |
| A3: dois multiplicadores e quadraturas | Mesmo: `nativeMixed_multiplier_orthogonal`; `NativeGammaMixedOrthogonality`: `nativeGammaMixedRay_complement_orthogonal` | N |
| A3: duas entradas, ambas ordens, colisão | `NativeGammaMixedOrthogonality`: `nativeGamma_mixed_complement_orthogonal`, `nativeGamma_complement_mixed_orthogonal` | N |
| A3: Gamma canônico inteiro e Gram | Mesmo: `nativeCanonicalGamma_mixed_complement_Gram`; `C3MixedReturnTraceObstruction`: `canonicalC3GammaState_eq_returnPart_add_remainder` | N/R |
| A3: complemento não nulo | `C3MixedReturnTraceObstruction`: `canonicalC3ReturnGammaRemainder_energy_pos` | R |
| A4: resposta geométrica e coordenadas | `NativeGammaMixedResponse`: `nativeMixedCauchy_camera_readout`, `nativeMixedCauchy_responseCoordinates` | N |
| A4: compressão e readout normalizado | Mesmo: `nativeMixedCauchy_compression`, `nativeMixedCauchy_unit_readout` | C |
| A4: kernel vetorial sem divisão | Mesmo: `nativeMixedGammaKernel`, `nativeMixedGammaKernel_greenIdentity` | N/C |
| B1: V original, norma, adjunto Hilbert | `NativeGammaNaimarkComplexProjection`: `nativeComplexNaimarkPort_eq_original`, `nativeComplexNaimarkPort_norm`, `nativeComplexNaimark_hilbertAdjoint` | N |
| B1: adjunto original e leitura Gamma | Mesmo: `nativeComplexNaimarkAdjoint_eq_original`, `nativeComplexNaimarkAdjoint_gamma` | N/C |
| B1: escape e ambas ortogonalidades | Mesmo: `nativeGammaGlobalEscape_roundtrip`, `nativeGammaGlobalEscape_orthogonal`, `nativeGammaGlobalEscape_orthogonal_reverse` | N |
| B2: vetor de três setores | `NativeGammaThreeSectorResolvent`: `nativeGammaResolvent_threeSector_roundtrip` | N |
| B2: todos os cruzamentos e Gram | Mesmo: `nativeGammaResolvent_camera_halo_orthogonal`, `nativeGammaResolvent_halo_camera_orthogonal`, `nativeGammaResolvent_threeSector_orthogonal`, `nativeGammaResolvent_threeSector_Gram` | N |
| B3: matrizes originais e adjunto hermitiano | `NativeGammaResolventMatrix`: `nativeGammaCauchyMatrix`, `nativeGammaHaloMatrix`, `nativeGammaEscapeMatrix`, `nativeSixCameraGram_isHermitian` | N |
| B3: identidade universal e divisão condicionada | Mesmo: `nativeGammaResolvent_matrixIdentity`, `nativeGammaResolvent_matrixIdentity_divided` | N/C |
| B3: parte imaginária hermitiana, sinal | Mesmo: `nativeGammaHermitianImaginary`, `nativeGammaResolvent_upperHalfPlane` | N/C |
| B3: Grams exteriores não negativos | `NativeGammaExteriorGramPositivity`: `nativeGammaExteriorGrams_nonnegative` | N |
| B4: mapas globais originais complexificados | `NativeGammaNaimarkHaloEscape`: `nativeComplexGlobalNaimarkProjection_eq_realComplexification`, `nativeComplexGlobalNaimarkEscape_eq_realComplexification` | N |
| B4: seis câmeras, halo e escape | Mesmo: `nativeComplexSixCameraNaimarkProjection_range`, `nativeComplexSixCameraNaimarkEscape_orthogonal`, `nativeGammaSixCameraEscape_eq_halo_add_globalEscape`, `nativeGammaSixCameraEscape_pairing` | N |
| C1: dois produtores Cauchy independentes | `NativeGammaMixedMaterialBalance`: `nativeCanonicalGammaMixedPair_literal`, `nativeCanonicalGammaComplementPair_literal` | N |
| C1: soma do par e de duas pernas | Mesmo: `nativeCanonicalGammaMixedPairs_roundtrip`, `nativeGammaMaterialAmbientPair_add` | N |
| C1: aditividade do defeito de gráfico | Mesmo: `nativeGammaMaterialAmbientDefect_add` | N |
| C2: zeros Green completos, não individuais materiais | Mesmo: `nativeGammaMixedPairs_Green_crossings`, `nativeGammaMixedPairs_materialCrossBalance` | C |
| C3: balanços cabeça + cauda, todos C,R | Mesmo: `nativeGammaMixedPairs_materialHeadTailCrossBalance` | C |
| C3: 36 pares e quatro setores independentes | `NativeGammaMaterialHeadTailLedger`: `nativeGammaWholePair_camera_fourHeadTails` | R |
| C3: capstone aplicado e probes fiéis | `NativeGammaMixedResolventCapstone`: `nativeGammaMixedTransport_capstone` | C |
| D1: ligação mista C6-C9 | `NativeGammaC9EnergyBound`: `nativeC9CauchyReadout_mixedDuality` | C |
| D1: probe complementar zero e misto=inteiro | Mesmo: `nativeC9CauchyReadout_complement_zero`, `nativeC9CauchyReadout_mixed_eq_full` | C |
| D2: energia exterior, sem/dividida | Mesmo: `nativeC9CauchyExterior_energy_bound`, `nativeC9CauchyExterior_energy_bound_divided` | N/C |
| D2: fonte canônica, cota estritamente positiva | Mesmo: `nativeCanonicalGammaCauchyExterior_energy_lower_bound`, `nativeCanonicalGammaCauchyExterior_energy_witness` | C |
| D3: variância exata e não negativa | `NativeGammaMixedVariance`: `nativeMixedGamma_ward`, `nativeMixedResolventVariance_exact`, `nativeMixedResolventVariance_nonnegative` | N/C |
| D3: cota C9 e positividade em 4+i/8 | Mesmo: `nativeMixedResolventVariance_C9_lower_bound`, `nativeMixedResolventVariance_witness_positive` | C |
| D4: parcela mista canônica | `NativeGammaMixedMismatchReduction`: `nativeCanonicalMixedGamma_Gram` | N |
| D4: coordenada aritmética literal | Mesmo: `nativeCanonicalGamma_cameraSix_eq_powers` | C |
| D4: mismatch já definido e Wronskiano correto | Mesmo: `nativeGammaMismatch_mixedComplementReduction` | C |
| D4: identificação com ledger corrigido | Mesmo: `nativeGammaMismatch_mixedReduction_materialLedger` | C |
| Capstone vetorial aplicado, exterior original | `NativeGammaMixedResolventCapstone`: `nativeGammaMixedResolvent_capstone` | C |
| Fronteira: no-go vestido preservado | `C3GammaCameraTraceObstruction`: `canonicalC3RawGammaWronskianDefect_ne_zero_near_imaginary_center`, `not_canonicalCompletedC3GammaCauchyScalarization_cameraFive` | R |

## Validação e publicação

A implementação acrescenta 16 módulos e 152 declarações públicas, com
16 audits correspondentes. O registro completo cobre 362 declarações em
36 módulos, incluindo as 210 anteriores. O verificador também exige que
todo módulo `NativeGamma*.lean` não audit seja registrado, impedindo a
omissão silenciosa de módulos novos.

Cada declaração tem `#check`, `#print axioms` e o guard transitivo
`#audit_physical_sewing`, que inspeciona os tipos e os corpos, inclusive
dependências privadas. Os únicos fundamentos aceitos são `propext`,
`Classical.choice` e `Quot.sound`. Não há `sorry`, `admit`, novos axiomas,
`unsafe` ou hipótese pública que postule a ortogonalidade ou mismatch zero.

Ambiente: `ssh llm`, Lean 4.32.0, Lake 5.0.0-src. O procedimento efetivo é:

```bash
export PATH=/home/thlinux/.elan/bin:$PATH
lake build CarrySelfAdjointOperator.NativeGammaMixedResolventCapstone --wfail
bash scripts/audit_gamma_cauchy_transport.sh .lake/mixed-resolvent-audit
```

O segundo comando executa inventário, checks de diff, todos os 36 builds
Audit com `--wfail`, todos os 36 audits diretos com `lean -E warning`,
SHA-256 das fontes, auditoria estática, build da raiz com `--wfail` e
`scripts/audit.sh`. Lean não aceita a opção `--wfail`; essa opção pertence
ao Lake. A chamada exploratória incorreta foi corrigida para `-E warning`.
Falhas ordinárias de elaboração foram resolvidas incrementalmente antes
da validação completa; os logs incrementais são preservados separadamente.

Validação integral pré-integração executada em `llm`, de
`2026-10-13T05:27:45Z` a `2026-10-13T05:45:55Z`, com saída zero:

- 36 builds Audit com `--wfail` e 36 audits diretos com `-E warning`;
- 362 raízes públicas verificadas; maior fechamento transitivo: 7134;
- apenas os três fundamentos aceitos, em todos os guards;
- inventário, checks de diff e auditoria estática aprovados;
- build da raiz com `--wfail`: 10166 jobs, sucesso;
- `scripts/audit.sh`: 8903 jobs, `kernel audit passed`.

O inventário inicial foi produzido antes da inclusão do corolário aritmético
`nativeCanonicalGamma_cameraSix_eq_powers` e registrava 361 declarações.
Ele foi preservado como `inventory-before-cameraSix-corollary.log`. O
inventário final e a soma efetiva das 36 raízes dos guards registram 362;
o corolário foi compilado e auditado nesta campanha. Não se conta uma
declaração apenas pela presença no registro.

Os logs completos estão em `.lake/mixed-resolvent-audit/` no ambiente de
validação e são arquivados na entrega antes de remover a worktree própria.
Os logs incrementais, inclusive erros ordinários já corrigidos, são
preservados separadamente. Hashes de publicação, resultados da CI externa
e a repetição integral pós-integração são registrados no manifesto da
entrega, sem confundir CI com Lean executado. Uma CI sem jobs não valida Lean.

## Primeira obrigação global restante

Permanece aberta a igualdade entre a resposta do complemento da fonte
canônica e a parcela necessária do Wronskiano nativo não vestido, de modo
a decidir a anulação global do mismatch já nomeado. A parcela mista agora
tem resposta explícita e os seus dois cruzamentos Gamma foram provados
zero; não se conclui daí a anulação do resto.

Também permanecem distintas as sementes do modo das cores e da meia
densidade radial, os relógios material/contínuo/alturas, os exteriores
nativo/global, as caudas Laguerre e os bordos Jacobi. Não há identificação
unitária dessas sementes, atualização dos pins, anulação do mismatch,
isometria multibase universal, completude Laguerre all-order, passagem
infinita ou positividade quiral global. O estudo do bordo Laguerre de seis
direções, a positividade estrita de δ em todo o domínio e a representação
integral adicional de k são extensões independentes, não hipóteses ocultas.

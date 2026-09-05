# Auditoria das coordenadas, do operador de altura e dos cortes C3

**Data da pesquisa:** 4 de setembro de 2026. **Servidor:** `llm`.
**Base inspecionada:** `carry-self-adjoint-operator`, branch `agent/projective-valve-moment-frontier`, commit `a52230c5cba4918fb5f05d00c8f31b27bc828d09`.
**Dependências consumidas:** CPFormal/primos `65d50f6db1208708e109982ba97e1d51d3039956`; NativeCarryC3Crosswalk `150cfc7fb08da96bf8117f15869cc2b819d593c2`.

A frase “os momentos do autoadjunto usam a variável de altura $t$” precisava ser corrigida. **Os $h_k$ são coeficientes da log derivada na variável $v=t^2$; no modelo de Jacobi, são momentos da variável espectral inversa quadrática. O operador de altura é obtido depois por $T=J^{-1/2}$.** O gerador material $\log n$ é outro objeto, cuja identificação com essa realização exige uma ponte demonstrada.

O script indicado por Thiago, `native_carry_height_moment_jacobi_operator_lab.py`, confirma essa distinção e fornece uma referência finita útil: fechamento de bordo, jets, Grams, energia positiva e dois kernels de Green. Reutilizamos suas funções com os momentos da construção theta nativa já arquivada. A identificação dessa energia com um readout geométrico independente permanece por construir.

## 1. Dicionário das variáveis

| Símbolo | Papel |
| --- | --- |
| $n$ | Índice material positivo. No Lean, algumas sequências usam $n+1$. |
| $L_n=\log n$ | Frequência do gerador da fase $e^{-it\log n}$. |
| $s=\sigma+it$ | Parâmetro do estado de amplitude e fase. |
| $t$ | Parâmetro de altura da característica completada $F(t)$. |
| $v=t^2$ | Variável da característica par $\Phi(v)$ e da log derivada $q(v)$. |
| $h_k$ | Coeficiente de $v^k$ em $q(v)=-\Phi'(v)/\Phi(v)$. |
| $\lambda$ | Variável de multiplicação de Jacobi. Sob o certificado do teorema espectral, $\lambda=t_0^{-2}$ corresponde à altura real não nula $t_0$ de um zero. |
| $J_N$ | Jacobi obtido dos momentos até o índice $2N-1$. |
| $T_N=J_N^{-1/2}$ | Operador finito de altura, quando $J_N$ é positivo definido. |

Escrevendo localmente

$$
F(t)=F(0)\Phi(t^2),\qquad
q(v)=-\frac{\Phi'(v)}{\Phi(v)}=\sum_{k\ge0}h_kv^k,
$$

temos

$$
a(t)=-\frac{F'(t)}{2F(t)}=tq(t^2).
$$

O Lean reconstrói a característica par sem dividir por $F(0)$. Essa normalização constante não altera a log derivada. O laboratório chama $-F'/F$ de `m`; nosso $a$ é `m/2`.

Fontes:

- [CompletedNativeWeylMoments.lean](../CarrySelfAdjointOperator/CompletedNativeWeylMoments.lean): `completedNativeEvenCharacteristicCoefficient`, coeficientes de ordem $2k$ de $F$.
- [CompletedNativeRealWeylMoments.lean](../CarrySelfAdjointOperator/CompletedNativeRealWeylMoments.lean): `canonicalCompletedNativeLogDerivativeMoment`, recorrência real.
- [CompletedNativeAnalyticMomentGrowth.lean](../CarrySelfAdjointOperator/CompletedNativeAnalyticMomentGrowth.lean): `completedNativeEvenCharacteristic`, `completedNativeLogDerivative` e `completedNativeLogDerivativeTaylorCoefficient_eq_canonical`.
- [CompletedNativeJacobiPointSpectrumConverse.lean](../CarrySelfAdjointOperator/CompletedNativeJacobiPointSpectrumConverse.lean): `completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_iff_nativeZero`. O argumento `certificate : CompletedNativeRealHPCarrierCertificate jet` é explícito.

Na realização positiva, $h_k=\langle u,J^ku\rangle=\int\lambda^k\,d\rho(\lambda)$. Na descrição atômica do script, a massa correspondente à altura $\gamma$ é $m_\gamma\gamma^{-2}$ em $\lambda=\gamma^{-2}$. A multiplicidade aparece no peso da medida cíclica; não é automaticamente a dimensão do autoespaço do Jacobi escalar. A descrição por traço exige a realização com multiplicidades tratada separadamente pelo próprio script.

## 2. Peças recuperadas do arquivo indicado

Fonte original preservada em [native_carry_height_moment_jacobi_operator_lab.py](../research/coordinate-cutoff-audit-2026-09-04/source/native_carry_height_moment_jacobi_operator_lab.py).

| Função/campo | Peça recuperada |
| --- | --- |
| `log_derivative_moments` | Mesma recorrência de divisão de séries que produz os $h_k$ canônicos. |
| `hankel_matrices` | $G_N=(h_{i+j})$, $K_N=(h_{i+j+1})$. |
| `jacobi_from_moments` | $G_N=L_NL_N^T$ e $J_N=L_N^{-1}K_NL_N^{-T}$. |
| `green_boundary_closure` | Fechamento da última coluna do shift monomial, selecionado por $h_{2N-1}$. |
| `defect_jet_realization` | $x_0=\sqrt{h_0}e_0$, $x_j=J_N^jx_0$, matriz de features $X_N=L_N^T$. |
| `green_energy_analysis` | $C_N=\operatorname{chol}(K_N)^T X_N^{-1}$ e $J_N=C_N^TC_N$. |
| `height_spectrum` | Constrói a matriz real simétrica $T_N=J_N^{-1/2}$. |

O fechamento não descarta a última coluna: $G_N^{-1}K_N$ é o shift monomial mais uma correção de posto um determinada pelos momentos. Esse $N$ é a ordem polinomial; não é o número de centros nem o horizonte material.

Para $\gamma_N(v)=(I-vJ_N)^{-1}x_0$ e $q_N(v)=\langle x_0,\gamma_N(v)\rangle$, o código verifica

$$
\frac{v q_N(v)-\overline{wq_N(w)}}{v-\bar w}
=\langle\gamma_N(w),\gamma_N(v)\rangle,
$$

$$
\frac{q_N(v)-\overline{q_N(w)}}{v-\bar w}
=\langle\gamma_N(w),J_N\gamma_N(v)\rangle.
$$

Na variável de altura, usamos explicitamente

$$
r_N(t)=(I-t^2J_N)^{-1}x_0,\qquad
\Psi_N(t)=\bigl(r_N(t),\,t\sqrt{J_N}r_N(t)\bigr),
$$

$$
a_N(t)=tq_N(t^2),\qquad
\langle\Psi_N(x),\Psi_N(z)\rangle
=\frac{a_N(z)-a_N(x)}{z-x},
$$

com diagonal $a_N'(x)$. Essa é a troca de variável necessária para comparar o kernel do script com o kernel de altura que buscamos.

**Uso para a costura:** comparar o readout geométrico, incluindo o bordo, com $C_N$ e com os estados $r_N(t)$. O laboratório constrói $C_N$ a partir dos momentos-alvo; ainda não demonstra que o TFVD geométrico produz essa mesma energia. Não devemos tratar essa construção como uma identificação geométrica independente.

## 3. Execução com os momentos nativos existentes

Executamos [audit_height_coordinates.py](../research/coordinate-cutoff-audit-2026-09-04/audit_height_coordinates.py) no servidor, com 220 dígitos e ordens $4,8,12,16$.

- Entrada: [native_moments.json](../research/geometric-kernel-search-2026-09-04/reference/native_moments.json), produzido pela quadratura theta e pela recorrência nativa.
- O original foi preservado byte a byte. Seu caminho `completed_xi`/Cauchy, que chama `mp.zeta`, não foi executado; `mp.zeta` e `mp.zetazero` foram bloqueados no wrapper para detectar uso acidental.
- Diferença relativa máxima na recorrência dos 80 momentos: menor que $7.95\times10^{-217}$.
- $G_N$ e $K_N$ positivos nos quatro testes.
- Diferença relativa máxima entre $\langle x_0,J_N^kx_0\rangle$ e $h_k$, para $0\le k<2N$: menor que $5.8\times10^{-220}$.
- Resíduo de $T_N^{-2}=J_N$: menor que $8.7\times10^{-222}$.
- Kernels em dois pontos e na diagonal: resíduos menores que $3.5\times10^{-223}$ nos pontos testados.
- Maior resíduo absoluto das verificações do fechamento: menor que $1.1\times10^{-155}$. Fatorações de jets e energia: menor que $1.1\times10^{-188}$.

O momento seguinte, de índice $2N$, já tem diferença não nula: aproximadamente $8.44\times10^{-6}$ em $N=4$ e $6.58\times10^{-39}$ em $N=16$, em termos relativos. Isso ilustra o alcance finito: a matriz reproduz o bloco de momentos usado na construção, mas não todos os momentos infinitos.

Resultados: [height_coordinates.json](../research/coordinate-cutoff-audit-2026-09-04/height_coordinates.json). Os resíduos medem consistência numérica; não são cotas certificadas por intervalos nem prova da positividade em todas as ordens.

## 4. $\log n$ e a rotação de 90 graus já estão presentes

O estado nativo é

$$
\psi_{\sigma,t}(n)=n^{-\sigma}e^{-it\log n}.
$$

Ele é indexado por $n$ e seu gerador de fase multiplica por $\log n$. Não encontramos omissão do logaritmo nessa definição.

- [CpRealSpectralOperator.lean](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpRealSpectralOperator.lean#L29): `realSpectralState`, `norm_realSpectralState`.
- [CpInfiniteRealSpectralGenerator.lean](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpInfiniteRealSpectralGenerator.lean#L41): `infiniteRealSpectralFrequency`, multiplicação por $\log(n+1)$ no domínio maximal.

Também existem os teoremas lembrados por Thiago:

- [CpConformalJacobian.lean](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpConformalJacobian.lean#L51): `conformal_deriv_t_eq_I_mul_deriv_sigma`, `conformal_norm_eq`, `conformal_orthogonal`, `conformal_positiveDirichletValue`.
- [CpNativeCarryRealPlaneComplexPackaging.lean](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L49): `normSq_nativeCarryRealPlaneComplexPackaging` e `nativeCarryRealPlaneComplexPackaging_finiteChartAt`, preservação de energia e compatibilidade com a câmera.
- [CpNativeCarryComplexOperatorSameAsReal.lean](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpNativeCarryComplexOperatorSameAsReal.lean#L67): `nativeCarryComplexOperatorBoundaryClosesAt_iff` e `isNativeCarryComplexOperatorZero_iff_real`.

A identidade é $\partial_t\psi=i\,\partial_\sigma\psi$. Ela importa para sinais e fatores dos jets. Empacotar $(x,y)$ como $x+iy$ conserva as duas coordenadas; tomar só a parte real não faz esse transporte. Uma rotação isométrica do estado inteiro preserva sua norma, de modo que não altera por si só uma desigualdade já estabelecida entre normas centrais.

O wrapper verificou numericamente o empacotamento real, a lei das derivadas e $|\psi|^2=1/n$, em seis índices e três alturas fixadas sem informação espectral. O maior resíduo foi menor que $1.3\times10^{-221}$.

Esses teoremas não identificam automaticamente $H_{\log}$ com $J$ ou $T$. Uma mudança não linear de coordenada espectral precisa carregar a medida, o observável e o vetor cíclico correspondentes.

## 5. Centros completos: um, dois e os dados de bordo

A dependência consumida contém [GeometricCutoffCompleteness.lean](https://github.com/thiagomassensini/native-carry-c3-crosswalk/blob/150cfc7fb08da96bf8117f15869cc2b819d593c2/NativeCarryC3Crosswalk/GeometricCutoffCompleteness.lean).

`IsGeometricallyCompleteNativeCutoff b M H` exige $b\ge2$, **$M\ge1$** e que a última perna direita caiba no horizonte $H$:

$$
H\ge4M+1\quad (C2),\qquad
H\ge bM+\lfloor b/2\rfloor\quad (b\ge3).
$$

| Câmera | Um centro completo | Dois centros completos |
| --- | --- | --- |
| C2, centros $4m$, raio 1 | $H\ge5$ | $H\ge9$ |
| C3, centros $3m$, raio 1 | $H\ge4$ | $H\ge7$ |
| Natural $b\ge3$ | $H\ge b+\lfloor b/2\rfloor$ | $H\ge2b+\lfloor b/2\rfloor$ |

Localizadores: `included_center_has_both_legs_in_window`, `center_only_horizon_is_not_complete`, `c2_one_complete_center_iff`, `natural_one_complete_center_iff`.

Para bases pares, o raio antipodal $b/2$ está incluído. `even_endpoint_records_head_tail_incidence` registra uma diferença importante: no último extremo, o coeficiente da câmera finita é 1, enquanto o perfil periódico infinito vale 2. Truncar o perfil periódico não substitui a câmera finita exata.

Um centro completo é a condição de admissão geométrica. A reconstrução TFVD de uma segunda diferença precisa também dos **dois dados de bordo**. São contagens diferentes. Em `weighted_tfvd_block`, as duas linhas de traço e todas as linhas interiores de três posições são mantidas. A presença de um centro, isoladamente, não é um teorema de reconstrução de um estado arbitrário.

Reexecutamos o laboratório antigo de completude em horizontes $16,32,64,128$, com altura de amostra $t=2$. Em $H=128$:

| Política | Bases admitidas | Brackets completos | Média normalizada do setor de brackets |
| --- | ---: | ---: | ---: |
| Todas as bases $2,\ldots,H$ | 127 | 3627 | 0,8068967650 |
| Pelo menos um centro completo | 84 | 3627 | 0,8670063854 |
| Regra conservadora $2b\le H$ | 63 | 2845 | 0,8961263369 |

Retirar câmeras sem centro remove sementes sem remover brackets completos no segundo caso; a normalização muda. **A política de admissão importa.** Esse teste não recalcula todos os 525 registros anteriores nem identifica a forma corrigida com os momentos nativos. Ele delimita uma interpretação que não pode ser transferida silenciosamente entre o laboratório vertical all-bases e a geometria horizontal.

Fonte e dados: [camera_completeness.json](../research/coordinate-cutoff-audit-2026-09-04/camera_completeness.json), [script original](../research/coordinate-cutoff-audit-2026-09-04/source/native_carry_camera_completeness_audit.py). As frases históricas emitidas automaticamente pelo script não são teoremas; a conclusão acima usa as linhas numéricas especificadas.

## 6. Cabeça, cauda e o alcance do resultado C3

A identidade escalar completada **inclui a cauda**:

- Na dependência, `complete_head_add_complete_center_tail` e `complete_head_add_complete_center_tail_eq_factor_mul_nativeScalar`.
- Em [CanonicalC3GlobalCameraBoundaryBridge.lean](../CarrySelfAdjointOperator/CanonicalC3GlobalCameraBoundaryBridge.lean): `canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout_eq_completed`, `canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout_eq_neg_deriv`, `canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout_eq_completed` e `canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion_eq_completed`.

Os readouts com cabeça e cauda recuperam o valor completado e o companheiro de derivada para todo $M$. Isso não diz que a cabeça sozinha já seja a função completada.

Também não se devem confundir:

1. A cauda escalar após o corte de centros.
2. Os dois traços para reconstruir um vetor TFVD finito.
3. A cauda de saída de um operador infinito: em geral, $(P_NAP_N)^*(P_NAP_N)$ difere de $P_NA^*AP_N$ pelo termo $P_NA^*(I-P_N)AP_N$, com $P_N$ ortogonal e produtos bem definidos.
4. O defeito de aproximação do jet de cabeça por jets deslocados, que aparece nos certificados de núcleo nulo.

Os candidatos TFVD finitos anteriores testavam matrizes e fontes específicas. A estabilidade de alguns momentos com o corte não os transforma automaticamente no operador nativo completado. No lado Jacobi há teoremas de compressão exata, como `closedGreenJetJacobiOperator_finiteCompression_eq_canonicalSection` em [GreenJetJacobiFiniteCompression.lean](../CarrySelfAdjointOperator/GreenJetJacobiFiniteCompression.lean), com os dados/certificados de sua construção. Isso não implica que $J_N^{-1/2}$ seja a compressão de $J^{-1/2}$.

O resultado central de [CompletedC3KernelMetricCalibration.lean](../CarrySelfAdjointOperator/CompletedC3KernelMetricCalibration.lean) compara o **estado Hilbert infinito específico com métrica de soma ortogonal padrão**:

$$
h_0<K_{\mathrm{C3,padrão}}(0,0).
$$

Sua energia ordinária já é maior que $1/16$, enquanto $h_0<1/16$. O argumento usa a norma de uma coordenada do gradiente infinito, não uma aproximação numérica nem a mera positividade de uma correção.

A prova anterior especializava o corte em $M=0$. Acrescentamos [CompletedC3GeometricCutoffCalibration.lean](../CarrySelfAdjointOperator/CompletedC3GeometricCutoffCalibration.lean), com quatro declarações:

- `canonicalCompletedC3AllCutoffOrientedRealKernelReadout_zero_zero`: o readout central é $h_0$ para todo $M$.
- `canonicalCompletedC3AllCutoffCentralReadout_re_lt_fixedKernel`: a desigualdade estrita vale para cada $M$.
- `canonicalC3_geometricallyCompleteCutoff_iff`: a condição C3 é $M\ge1$ e $H\ge3M+1$.
- `not_canonicalCompletedC3CentralSewing_on_twoCompleteCenters`: mesmo restringindo a pelo menos dois centros completos, há contradição; o testemunho usa $M=2$, $H=7$.

**Alcance:** isso exclui a métrica fixa daquele estado, inclusive nos cortes admissíveis. Não exclui outra métrica positiva, cruzamentos diferentes ou outro estado geométrico. A diagonal do readout escalar foi definida pela extensão removível da derivada nativa; o teorema não constitui uma construção independente dessa diagonal como Gram geométrico.

As orientações complexas aparecem explicitamente em [CompletedC3RawSpectralTraceTransport.lean](../CarrySelfAdjointOperator/CompletedC3RawSpectralTraceTransport.lean) e [CompletedC3CausalGreenGramSewing.lean](../CarrySelfAdjointOperator/CompletedC3CausalGreenGramSewing.lean), em particular `canonicalCompletedC3NormalizedGreenLimitTrace_eq_globalBoundary_iff_causalEnergy`. Essa última declaração reduz uma igualdade específica de traços à igualdade das energias com fatores/orientações já transportados; não identifica por si só todas as energias nativas.

## 7. Peças concretas para continuar

O script de altura fornece o referencial finito $x_0$, $J_N$, $C_N$ e o fechamento da última coluna. O próximo confronto geométrico deve explicitar o mapa entre os estados e verificar simultaneamente

$$
\langle u,V^ku\rangle=h_k,\qquad
a(t)=t\langle u,(I-t^2V)^{-1}u\rangle,
$$

com os bordos e o transporte de escala incluídos. Se a proposta partir de $H_{\log}$, é necessário especificar qual função dele, qual compressão/acoplamento e qual fonte produzem $V$.

Uma conjugação por isometria, preservando fonte e operador, transportaria esses produtos na realização correspondente. Substituir $\lambda$ por $\log\lambda$, ou inverter/quadrar um operador, altera os momentos correspondentes; deve-se acompanhar essa alteração na medida e no readout. Essa é a comparação precisa a fazer, sem usar a expressão ambígua “o autoadjunto está sobre $t$”.

O kernel nativo geométrico completo continua aberto nesta rodada. O novo resultado Lean elimina a dúvida específica sobre cortes vazios na comparação da métrica C3 padrão; os testes e o arquivo de altura tornam mais precisa a rota de construção.

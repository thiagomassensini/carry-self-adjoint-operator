# Ponte da válvula Green–multiplicativa aos momentos nativos

Conferência de 2026-09-05, a partir da sequência de commits e da PR #23 indicada por Thiago.

## Resultado

**Sim: essa é a ponte algébrica que liga Green, potencial logarítmico e massa multiplicativa.** Ela já está demonstrada e integrada. Nesta conferência, aplicamos essa infraestrutura à sequência de momentos efetivamente usada pelo autoadjunto e acrescentamos uma identidade Lean sem hipótese de positividade:

$$
\operatorname{projectiveValveMass}\!\left(\sum_{n\ge0}h_n v^n\right)
=
\left(\frac{\Phi(v)}{\Phi(0)}\right)^{-1}.
$$

Aqui $F(t)=\Phi(t^2)$ é a característica completada nativa e os $h_n$ são os coeficientes já definidos por $q(v)=-\Phi'(v)/\Phi(v)$. A igualdade acima é de **séries formais**. Não depende de uma nova identificação analítica por avaliação numérica.

A identificação escalar foi obtida reutilizando a recorrência nativa e a unicidade da válvula. O passo de realizar esses mesmos coeficientes como produtos internos da geometria continua separado e explícito.

## 1. A sequência indicada já está no projeto

A [PR #23](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/23) está **MERGED**, com merge `696bb93ce8ce951555af52894d3fae2a12e5ee0c` em 2026-09-03 20:06:01 UTC, isto é, 17:06:01 GMT-3. O commit está na ancestralidade do branch de trabalho. Os títulos enviados foram conferidos diretamente em Git.

| Commit / módulo | Resultado reutilizável |
| --- | --- |
| `8641438`, `MultiplicativeValve` | Soma de canais corresponde ao produto de massas |
| `f65d044`, mesmo módulo | Exponencial formal com seu canal de log derivada |
| `64aa034` e `d672b04`, `DiscreteValveSeries` | Diferenças/brackets no anel de séries e reconstrução Green |
| `6309b0e`, `DiscreteValveSeries.mk_greenSum` | Soma Green = convolução pelo núcleo $X/(1-X)^2$ |
| `a317612`, `MultiplicativeValve.mk_towerMass_eq_expSeries` | $\operatorname{towerMass}(b)=\exp(\sum_{n\ge1}b_nX^n/n)$, para $b_0=0$ |
| `a50ddd7`, `CanonicalTowerChannel` e `ProjectiveDepthEquivalence` | Canal extraído e massa integrada são inversos; coordenada projetiva é invertível |
| PR #23, `GreenMultiplicativeValveBridge` | Derivada do potencial Green na coordenada projetiva = curvatura transportada |

Desenvolvimentos posteriores já presentes:

- [GreenMultiplicativeValveMass](../CarrySelfAdjointOperator/GreenMultiplicativeValveMass.lean): `derivative_projectiveGreenMass`.
- [ProjectiveValveFundamentalTheorem](../CarrySelfAdjointOperator/ProjectiveValveFundamentalTheorem.lean): `projectiveValveMass_unique`.
- [ProjectiveValveEquivalence](../CarrySelfAdjointOperator/ProjectiveValveEquivalence.lean): `projectiveValveCurvature_projectiveValveMass`.
- [ProjectiveValveAlgebra](../CarrySelfAdjointOperator/ProjectiveValveAlgebra.lean): `projectiveValveMass_neg`, `projectiveValveMass_add`.
- [CompletedC3ValveNaturality](../CarrySelfAdjointOperator/CompletedC3ValveNaturality.lean): o bloco Cp efetivo entra na decomposição aditiva das curvaturas; sua massa é o produto das massas dos canais.

Logo, “construir a ligação aditivo–multiplicativo” não deve constar como uma pendência geral. A questão útil é qual curvatura e qual métrica entram nessa ligação.

## 2. Sinal, normalização e índices exatos

O novo fonte [NativeMomentProjectiveValveBridge](../CarrySelfAdjointOperator/NativeMomentProjectiveValveBridge.lean) define:

$$
\widehat\Phi(v)=\frac{\Phi(v)}{\Phi(0)},\qquad
Q(v)=\sum_{n\ge0}h_n v^n.
$$

A recorrência nativa já provada implica, coeficiente a coeficiente,

$$
\widehat\Phi'=-Q\widehat\Phi.
$$

Pela unicidade da solução da válvula, seguida da lei de inversão:

$$
\widehat\Phi=\operatorname{Valve}(-Q),
\qquad
A=\widehat\Phi^{-1}=\operatorname{Valve}(Q),
\qquad
A'=QA,\quad A(0)=1.
$$

O canal de torre usa a derivada graduada $vA'/A$. Portanto, a leitura dos coeficientes dá

$$
B(v)=vQ(v),\qquad b_0=0,\qquad b_{n+1}=h_n.
$$

Esta última fórmula é a leitura algébrica da definição de `IsLogDerivChannel`. No fonte novo, as identidades verificadas pelo kernel estão explicitadas nas declarações abaixo.

| Declaração nova | Garantia |
| --- | --- |
| `normalizedCompletedNativeEvenFormalSeries_constantCoeff` | Normalização exatamente igual a um |
| `derivative_completedNativeEvenFormalSeries` | $\Phi'=-Q\Phi$ para os coeficientes nativos reais |
| `derivative_normalizedCompletedNativeEvenFormalSeries` | A mesma equação após normalização |
| `normalizedCompletedNativeEvenFormalSeries_eq_valveMass_neg` | $\widehat\Phi=\operatorname{Valve}(-Q)$ |
| `projectiveValveMass_nativeMoments_eq_reciprocal` | $\operatorname{Valve}(Q)=\widehat\Phi^{-1}$ |
| `projectiveValveCurvature_nativeReciprocal_eq_moments` | Extrair a curvatura de $\widehat\Phi^{-1}$ recupera $Q$ |
| `isNativeMomentSequence_iff_valveMass_eq_nativeReciprocal` | Uma sequência proposta é a sequência nativa se, e somente se, sua massa de válvula é $\widehat\Phi^{-1}$ |
| `projectiveGreenMass_eq_nativeReciprocal_iff` | Para uma curvatura original $C$, sua massa Green projetiva é a massa nativa se, e somente se, $\operatorname{toProjective}(C)=Q$ |

Não há hipótese de positividade nas seis primeiras declarações. A existência e unicidade da sequência nativa já estavam demonstradas; esta aplicação as conecta diretamente à infraestrutura citada por Thiago.

## 3. O que isso permite fazer na busca geométrica

Há agora uma comparação formal exata para o candidato geométrico $C_{\rm geom}$:

$$
\operatorname{projectiveGreenMass}(C_{\rm geom})
=
\frac{\Phi(0)}{\Phi(v)}
\quad\Longleftrightarrow\quad
\operatorname{toProjective}(C_{\rm geom})=Q(v).
$$

Podemos trabalhar pelo lado da massa completa ou pelo lado da curvatura transportada, conforme a identidade mais acessível no ledger.

A mudança da válvula é $Y=X/(1-X)$. Na construção original de incidências, $X$ codifica profundidades; em $Q(v)$, $v=t^2$ codifica a variável par da característica. O anel formal permite comparar as séries, mas a interpretação geométrica exige demonstrar o transporte correspondente. Dar o mesmo nome à indeterminada não executa esse transporte.

Para obter o kernel positivo, a mesma realização deve ainda satisfazer

$$
\langle u_i,u_j\rangle=h_{i+j},
\qquad
\langle w_i,w_j\rangle=h_{i+j+1},
$$

com independência em toda ordem. Alternativamente, a rota do observável simétrico pode demonstrar $m_n=\langle u,S^{2n}u\rangle=h_n$ e a independência da órbita. A nova equivalência permite substituir essa igualdade de sequências por uma igualdade de massas; não acrescenta por si uma forma quadrática à equivalência algébrica.

A cadeia C3 já é mais concreta que uma analogia: [CompletedC3ValveGreenNaturality](../CarrySelfAdjointOperator/CompletedC3ValveGreenNaturality.lean) identifica ledger, port Green, fonte Gamma e par escalar $(-F',F)$ do mesmo estado. A preservação da forma Green entre as projeções é explicitada em [CompletedC3ValveCauchyNaturalityFrontier](../CarrySelfAdjointOperator/CompletedC3ValveCauchyNaturalityFrontier.lean). Essas declarações devem ser avaliadas junto da métrica e das correções de retorno do candidato, com o alcance das calibrações já demonstradas.

## 4. Verificação e continuidade

O módulo novo foi incluído no import geral e em `KernelConstructionAudit`, com as oito declarações na auditoria de axiomas. O build específico com `--wfail` e as 14 etapas de `scripts/audit.sh` passaram. Os resultados usam somente `propext`, `Classical.choice` e `Quot.sound`; não foi acrescentado escape de confiança.

Evidência desta rodada: [auditoria](../research/native-moment-valve-bridge-2026-09-05/verification.json). Os snapshots principais continuam `main=4de44de2341089a29665917ed48cd388c68a85e5` e base de trabalho `e176afaa6e5b9226c8f222e57a22f31e27a279df`, antes deste acréscimo. Os pins não foram alterados. Não foi acompanhado CI do GitHub.

Relacionados: [mapa HP](mapa-notas-hp-jets-retorno-atualizado.md), [rota projetiva](mapa-rota-valvula-projetiva.md), [identificação geométrica](identificacao-geometrica-kernel-carry.md).

## Continuidade em 2026-09-05: realização Hilbert e readout

Integração dos três módulos R/B recuperados e construção do [kernel Hilbert R/B e readout completado](c3-projective-hilbert-readout-kernel.md): produto interno polarizado preservado no limite, readout com cauda exata igual à característica nativa e massa formal identificada. A métrica do estado original tem massa central diferente de $h_0$; a construção do observável e da fonte que realizem a massa nativa continua explícita. O mapa registra o alcance exato e a interface Lean para o certificado.

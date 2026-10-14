# Extensão dos portos de energia a uma dimensão finita arbitrária

## Resultado e limite

`CompletedNativeChiralReturnArbitraryOrder.lean` estende o mecanismo de
transporte a qualquer dimensão finita. A conclusão positiva em todas as ordens
continua **condicional à positividade estrita das formas de bordo nativas**.
O módulo não prova essa família de desigualdades. O resultado incondicional
anterior para sete fontes permanece válido e passa explicitamente a todos
os seus prefixos.

Não se altera a métrica de Cauchy, a completação, os coeficientes ou as
amplitudes. Os momentos não definem os novos portos. Usa-se o defeito do
retorno original, como em `CompletedNativeChiralReturnEnergyPort.lean`.

## Ligação nova

Escreva `E_D(x) = nativeSourceFiniteBoundaryEnergy D x`, `J_(n,k)` para
`nativeSourceChiralJetInput n k` e `S_k(c) = Re(storage k c 1)`.

1. A forma `E_D` é contínua. A homogeneidade quadrática já existente,
   junto com a compacidade da esfera unitária, fornece a equivalência, para
   cada `D` fixo:

   \[
   (\forall x\ne0,\ E_D(x)>0)
   \iff
   \exists\varepsilon_D>0,\ \forall x,\
      \varepsilon_D\|x\|^2\le E_D(x).
   \]

   A escolha de `ε_D` ocorre depois de `D`, antes de `x`. A prova inclui `D=0`.

2. A estimativa de erro já formalizada controla todas as direções de uma vez:

   \[
   |2S_k(J_{n,k}x)-E_{2n}(x)|\le\eta\|x\|^2
   \]

   eventualmente em `k`, para cada `n` e cada `η>0`. Com `η=ε/2`, a nova
   ligação prova

   \[
   S_k(J_{n,k}x)\ge\frac{\varepsilon}{4}\|x\|^2.
   \]

   A bijetividade eventual do mapa geométrico `J_(n,k)` cobre **todos** os
   coeficientes originais. Resultam armazenamento estritamente positivo para
   toda entrada não nula e `‖radialReturnTransfer k (2*n)‖ ≤ 1`.
   A margem acima se refere à coordenada geométrica `x`; não se afirma uma
   constante uniforme na norma dos coeficientes originais, nem em `n` ou `k`.

3. A inclusão por zeros de `N` fontes em `M≥N` preserva separadamente os
   **dois vetores completos**: síntese incidente e síntese retornada. Preserva,
   portanto, o armazenamento e faz a contratibilidade descer aos prefixos.
   Isso permite usar uma margem em dimensão `2N` para obter o resultado em
   qualquer `N`, inclusive ímpar. Essa margem em `2N` é uma condição suficiente;
   não é declarada necessária para o bloco de tamanho `N`.

4. Sob essa margem explícita, os portos físicos existentes satisfazem,
   eventualmente, a igualdade com **todas as entradas** do kernel radial
   nativo de tamanho `N×N`. Para quaisquer ordens independentes `a,b<N`,

   \[
   \langle P_{k,N,a},P_{k,N,b}\rangle
   \longrightarrow
   \operatorname{polarizedGreenMomentCoefficient}(h,a,b).
   \]

   Trata-se da convergência do Gram completo, incluindo os cruzamentos.
   A regularidade é fornecida pela fonte canônica existente.

## Quantificadores e obrigação de sinal

O teorema de família tem a forma

\[
\bigl[\forall n,\ \forall x\ne0,\ E_{2n}(x)>0\bigr]
\Longrightarrow
\forall N,\ \exists K_N,\ \forall k\ge K_N,\ \|T_{k,N}\|\le1.
\]

Não há um único `K` afirmado para todas as dimensões. As hipóteses de
positividade são argumentos explícitos dos teoremas; não são novos axiomas.
A prova também estabelece uma condição necessária mais fraca:

\[
\bigl[T_{k,2n}\text{ eventualmente contrativo}\bigr]
\Longrightarrow \forall x,\ E_{2n}(x)\ge0.
\]

Logo, uma direção de bordo estritamente negativa impediria a contratibilidade
eventual nessa mesma dimensão. Nenhuma direção negativa é produzida aqui.
A não negatividade isolada não é usada para inferir uma margem estrita.

O conteúdo de `E_(2n)` é a soma dos dois blocos de momentos nativos, com as
fases herdadas, na identidade existente
`nativeSourceFiniteBoundaryEnergy_even_split`. O sinal em todas as ordens
não é uma mera estimativa de cauda. A infraestrutura de dominância quiral e
Stieltjes em `CompletedNativeChiralHankelDominance.lean` já identifica o
problema de positividade das torres de coeficientes. Não se assume que uma
certificação finita prove essa família infinita.

## API principal

- `nativeSourceFiniteBoundaryEnergy_pos_iff_margin`
- `radialIncidentSynthesis_pad`, `radialReturnedSynthesis_pad`
- `radialReturnTransfer_norm_le_one_of_prefix`
- `radialReturnTransfer_eventually_norm_le_one_of_le_seven`
- `storage_one_chiralJetInput_eventually_margin`
- `storage_one_even_eventually_pos_of_boundary_margin`
- `radialReturnTransfer_eventually_norm_le_one_of_boundary_margin`
- `nativeSourceFiniteBoundaryEnergy_nonneg_of_eventually_contractive`
- `not_eventually_contractive_of_negative_boundary_direction`
- `radialReturnSampleEnergyPort_eventually_kernel_of_boundary_margin`
- `radialReturnEnergyJet_inner_tendsto_of_boundary_margin`
- `radialReturnTransfer_all_orders_of_strict_boundary_positivity`

Todos estão em `CarrySelfAdjointOperator.ChiralReturn`. A auditoria dedicada
imprime axiomas e verifica a clausura de dependências de todas as declarações
públicas novas.

## O que permanece aberto

- A prova do sinal estrito de `E_(2n)` para todo `n`.
- Uma costura coerente dos vetores quando `N` varia ou um limite dos vetores.
- A identificação com um operador autoadjunto global de alturas e seu resolvente.
- Um limiar ou uma margem uniformes na dimensão.

Não foi executada nova campanha numérica, nem se deduziu convergência de
resolventes infinitos de identidades entre Grams finitos.

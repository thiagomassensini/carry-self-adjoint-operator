# Colisão conjugada, derivada central e acoplamento com completion

Data: 13/10/2026. Repositório: `thiagomassensini/carry-self-adjoint-operator`.
Base efetiva: `3d8ea36e504bf24769ef9cc53e7337d48dc9c819`, merge do PR #81.

## Proveniência e resultado

O pedido colado foi lido integralmente, incluindo a derivação, as APIs e
a seção de implementação. SHA-256 do arquivo:
`58491fc2df4e5ef685ccc148ecf399e1fa591e1f13b31ff3e880235129f3680d`.
O relatório do PR #81 e todos os módulos centrais solicitados foram
conferidos no checkout. Não foi localizada uma prova anterior equivalente
da não anulação central ou da negação da compatibilidade source-locus atual.

HEAD e origin/main coincidiam com a base. A PR #62 aberta trata de outra
obrigação. Não foram encontradas instruções AGENTS adicionais nos ancestrais
ou no repositório. A worktree própria é `/home/thlinux/carry-conjugate-collision`,
branch `agent/conjugate-collision-native-obstruction`. O cache foi copiado,
sem hardlinks. Os dois arquivos C2 não rastreados e as três worktrees
preexistentes permanecem fora das alterações.

Pins preservados:

| Dependência | Commit |
|---|---|
| Mathlib | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| NativeCarrySpectralWeyl | `298d83c9351e308a5213b9f5ac32e44087f98a9f` |
| NativeCarryC3Crosswalk | `150cfc7fb08da96bf8117f15869cc2b819d593c2` |
| CPFormal | `65d50f6db1208708e109982ba97e1d51d3039956` |

Cinco módulos novos, com 43 declarações públicas e seus cinco audits,
estendem o registro de 362 para 405 declarações, em 41 módulos. As listas
das primeiras 36 entradas foram comparadas com a base e são idênticas.
Nenhum produtor, Gram, carrier, clock, normalização ou definição do
mismatch existente foi alterado.

**Conclusão matemática:** a compatibilidade universal atual é falsa.
A construção de um transporte conjunto correto permanece aberta. Este
resultado não é uma impossibilidade de todo transporte, realização
autoadjunta ou teoria do carry.

## Definições e orientação

Escreva `N = nativeHeightScalar`, `A = nativeXiCompletionFactor`,
`F = completedNativeOperatorCharacteristic` e `s(z)=1/2+iz`. Literalmente,

\[
 A(z)=\tfrac12s(z)(s(z)-1)
       e^{-s(z)\log\pi/2}\Gamma_{\mathbb C}(s(z)/2),\qquad F=AN.
\]

Os companions são `C_N=-N'`, `C_A=-A'`, `C_F=-F'`; o par nativo é
`(C_N,N)`, não `(N,C_N)`. A primeira entrada do inner é antilinear e

\[
 g_{nat}((a,b),(a',b'))=\langle b,a'\rangle-\langle a,b'\rangle,
 \quad W_N(w,z)=C_N(w)\overline{N(z)}-N(w)\overline{C_N(z)}.
\]

A proposição REFUTADA é exatamente a definição existente
`CanonicalCompletedC3NativeSourceLocusGreenCompatibility`:

```lean
∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
  CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt z w hz hw
```

A relação pointwise compara os dois Green forms projetados do mesmo
estado estruturado: Gamma e escalar nativo não vestido. Ela não exclui
pares conjugados e não é a representação positiva histórica de C3.

## A. Colisão sem divisão

Os vetores originais `canonicalCompletedC3PolarizedGammaState` permanecem
inteiros. O readout já certificado é

\[
 G_\Gamma(z,w)=(w-\overline z)\langle\gamma_z,\gamma_w\rangle.
\]

Para `z.im ≠ 0`, `conj z` também está fora do eixo real. Portanto,

\[
 G_\Gamma(z,\overline z)=0.
\]

Se ambos os height parameters pertencem à faixa Genuine, a igualdade
existente entre mismatch e readout menos Wronskiano fornece

\[
 \boxed{\operatorname{Mismatch}(z,\overline z)=-W_N(\overline z,z).}
\]

O lado esquerdo é o ORIGINAL
`canonicalCompletedC3NativeSourceLocusProjectionMismatch`. Não se define
um mismatch substituto, não se divide pela separação e não se atribui
um estado Gamma ao eixo real.

A identidade sem divisão do kernel misto do PR #81 implica
`conj (r_*(z))-r_*(conj z)=0`. Assim, os readouts Green misto e
complementar da redução também são zero na colisão. Isso não apaga
seus vetores ou os cruzamentos materiais individuais.

Para `z=it`, `w=-it`, `0<|t|<1/2`, as provas de admissibilidade produzem
`z.im=t`, `w.im=-t`, `s(z).re=1/2-t`, `s(w).re=1/2+t`; os dois últimos
pertencem a `(0,1)`. Segue a versão aplicada `Mismatch(it,-it)=-W_N(-it,it)`.

## B. Derivada central incondicional

1. `Real.Gamma_strictAntiOn_Ioc.antitoneOn.derivWithin_nonpos` dá a
   derivada não positiva dentro de `(0,1]`. O intervalo contém uma
   vizinhança de `1/4`, portanto `derivWithin_of_mem_nhds` a identifica
   com a derivada ordinária: `Gamma_R'(1/4) ≤ 0`. Não se deduz uma
   derivada estritamente negativa da monotonicidade estrita.
2. A diferenciabilidade complexa em `1/4` vem da exclusão de todos os
   polos `-m`. Aplicando `HasDerivAt.real_of_complex` e
   `Complex.Gamma_ofReal`, obtém-se
   `Re Gamma_C'(1/4)=Gamma_R'(1/4)`.
3. A regra do produto diferencia a definição literal de A. O fator
   polinomial tem derivada zero no centro, e as outras duas derivadas
   conservam seus fatores `I/2`. O resultado é

\[
 A'(0)=-\frac{i}{16}e^{-\log\pi/4}
       [\Gamma_{\mathbb C}'(1/4)-(\log\pi)\Gamma_{\mathbb C}(1/4)],
\]

\[
 \boxed{\Im A'(0)=\frac{e^{-\log\pi/4}}{16}
       [(\log\pi)\Gamma_{\mathbb R}(1/4)-\Gamma_{\mathbb R}'(1/4)]>0.}
\]

Usam-se apenas positividade da exponencial, `2 ≤ pi` (logo `log pi>0`),
`Real.Gamma_pos_of_pos` e a derivada não positiva. A parte imaginária
da derivada complexa de Gamma não precisa ser determinada.

O cancelamento certificado `A'(0)N(0)+A(0)N'(0)=0`, junto de `N(0)≠0`,
implica `N'(0)≠0`: a hipótese contrária produziria `A'(0)N(0)=0`.
Não se usa `A(0)≠0` nessa implicação.

As reflexões centrais já existentes, `conj N(0)=N(0)` e
`conj N'(0)=-N'(0)`, dão

\[
 \boxed{W_N(0,0)=-2N(0)N'(0)\ne0.}
\]

Todas essas não anulações são incondicionais, não campos de uma estrutura
de compatibilidade. Não há avaliação numérica de Gamma, N, F ou zeta.

## C. Família e refutação universal

`nativeConjugateWronskian t` é a função ESCALAR `W_N(-it,it)`, inclusive
em zero. Sua continuidade em zero usa a analiticidade local de N e de
sua derivada, composição com os dois parâmetros, conjugação e produtos.
Gamma não aparece nessa prova de continuidade.

Como seu valor central é não nulo, existe `epsilon>0`, `epsilon≤1/2`,
tal que para TODO `0<t<epsilon` a prova fornece parâmetros off-axis,
ambos na faixa Genuine, e

\[
 \boxed{\operatorname{Mismatch}(it,-it)\ne0.}
\]

Também se fornece um contraexemplo com `0<t<delta` para qualquer `delta>0`.
Isso refuta explicitamente a proposição original universal e sua versão
restrita à faixa Genuine. Separadamente, a nova não anulação de N' fecha
o corolário histórico `not_nativeC3GreenRepresentationOn`: a representação
positiva finita C3 literal também é refutada. São dois alvos distintos.

Um corolário adicional certifica o limite do MISMATCH ORIGINAL, não apenas
de um alias. Seu domínio é o subtipo de parâmetros `0<|t|<1/2`; o filtro
é a pré-imagem das vizinhanças de zero pela coordenada real. Sua não
trivialidade (`NeBot`) é provada construindo uma amostra admissível em
cada vizinhança. Nesse domínio,

\[
 \lim_{t\to0}\operatorname{Mismatch}(it,-it)=2N(0)N'(0)\ne0.
\]

Não há extensão artificial de Gamma em `t=0`. A investigação de uma
NOVA proposição universal que exclua a colisão continua distinta: não
se afirma sua refutação aqui sem uma prova de continuidade local de Gamma.

## D. Ledger e acoplamento físico

`nativeGammaMaterialLedgerTotal` apenas nomeia a expressão literal
certificada, sem definir qualquer corretor:

\[
 -\mathcal M-\mathcal A-v^*H\eta'+\eta^*Hv'-2\mathscr N_{scal}.
\]

`nativeGammaMaterialHeadTailLedgerTotal` nomeia o lado direito da versão
head/tail existente, conservando o gráfico radial, os DOIS produtos mistos,
seus termos de cauda e o defeito de métrica. As igualdades com o mismatch
original valem para entradas `z,w` independentes e TODOS os cutoffs C,k,R.

Na família construída, ambos os totais são não nulos para todos os
cutoffs, inclusive C=0. Não se distribui a não anulação entre parcelas.
Com C≥1, o transporte original continua reconstruindo os dois pares
Gamma completos nos mesmos contraexemplos. Essa condição é necessária
ao decoder, não à não anulação dos ledgers.

O cancelamento central antigo agora é certificado como NÃO TRIVIAL:

\[
 A(0)C_N(0)\ne0,\quad C_A(0)N(0)\ne0,
 \quad A(0)C_N(0)+C_A(0)N(0)=0,
\]

\[
 \boxed{|N(0)|^2W_A(0,0)+|A(0)|^2W_N(0,0)=0,}
\]

com ambos os termos ponderados não nulos. Daí também `W_A(0,0)≠0`
e a correção arquimediana orientada central não nula. Isso não é uma
soma de normas positivas independentes.

No carrier Cauchy ORIGINAL, o teorema aplicado às fontes existentes fornece

\[
 C_{source}=C_{native\ dressed}+C_{completion},
\]

\[
 I=C_{native\ dressed}+C_{completion}+iV_{source},\quad
 O=C_{native\ dressed}+C_{completion}-iV_{source}.
\]

As sínteses à esquerda são as incident/returned originais, com os mesmos
coeficientes e potências materiais. Os dois companions mantêm o denominador
Hermite-Biehler original e as colunas físicas. Exige-se faixa Genuine para
a regra do produto e denominador positivo não nulo SOMENTE para reconstruir
as pernas. Nenhuma dessas hipóteses radiais é acrescentada à obstrução Gamma.

O novo `nativeCoupledCompletion_source_polarized_product_sum` conserva
duas entradas realmente independentes: tamanhos N,M, profundidades k,l,
coeficientes c,d e raios r,s. N,M aqui são cardinalidades de amostras,
não o cutoff TFVD. Com `a_i,b_j` os coeficientes divididos pelos respectivos
denominadores originais, ele prova

\[
 \langle V_c,C_d\rangle-\langle C_c,V_d\rangle
 =\sum_{i,j}\overline{a_i}b_j\langle\psi_{k,i},\psi_{l,j}\rangle
 [\overline{A(z_i)}A(w_j)g_N(z_i,w_j)+\mathcal A_{arch}(z_i,w_j)].
\]

Cada crossing físico é completo; nenhuma cabeça curta substitui seu Gram.
A identidade é posterior às sínteses vetoriais. As identidades TFVD
tail-completed de `CompletedNativeChiralReturnCompletionSplit` continuam
as referências desses dois canais; nenhum novo produtor é definido por
"alvo menos resultado".

## Auditoria requisito por requisito

Todos os arquivos abaixo estão em `CarrySelfAdjointOperator/` e as novas
declarações no namespace `CarrySelfAdjointOperator.GammaMaterialSewing`.
N = prova nova; C = composição/corolário; R = resultado anterior preservado.

| Requisito | Arquivo e declaração | Status |
|---|---|---|
| A: admissibilidade de conj z | `NativeGammaConjugateCollisionIdentity`: `nativeConjugate_offAxis` | N |
| A: readout inteiro zero sem divisão | Mesmo: `nativeGammaConjugate_boundaryReadout_zero` | C |
| A: resposta mista e complemento | Mesmo: `nativeGammaConjugate_mixedResponse_zero`, `nativeGammaConjugate_mixedComplementReadouts_zero` | C |
| A: mismatch ORIGINAL na colisão | Mesmo: `nativeSourceLocusMismatch_conjugateCollision` | C |
| A: it,-it e provas de faixa | Mesmo: `nativeImaginaryCollision_admissible`, `nativeSourceLocusMismatch_imaginaryCollision` | N/C |
| B1: derivada real não positiva | `NativeGammaCenteredDerivative`: `realGamma_quarter_deriv_nonpos` | N |
| B2: restrição real da derivada | Mesmo: `complexGamma_quarter_hasDerivAt`, `complexGamma_quarter_deriv_re` | N |
| B3: derivação literal de A | Mesmo: `nativeXiCompletionFactor_deriv_zero_formula`, `_im_formula`, `_im_pos` | N |
| B4: A' não zero, incondicional | Mesmo: `nativeXiCompletionFactor_deriv_zero_ne_zero` | C |
| B5: N' não zero, incondicional | Mesmo: `nativeHeightScalar_deriv_zero_ne_zero` | C |
| B6: W_N central, valor e não zero | Mesmo: `nativeHeightScalar_centerWronskian_eq`, `_ne_zero` | N/C |
| C: função escalar e continuidade | `NativeGammaConjugateCollisionObstruction`: `nativeConjugateWronskian`, `_continuousAt_zero`, `_eventually_ne_zero` | N |
| C: TODO t suficientemente pequeno | Mesmo: `nativeSourceLocusMismatch_conjugateCounterexampleFamily` | N |
| C: aproximação arbitrária | Mesmo: `nativeSourceLocusMismatch_counterexamples_arbitrarily_close` | C |
| C: negação da proposição EXISTENTE | Mesmo: `not_canonicalCompletedC3NativeSourceLocusGreenCompatibility` | C |
| C: negação restrita à Genuine | Mesmo: `not_nativeSourceLocusGreenCompatibility_genuineStrip` | C |
| C: corolário positivo C3 distinto | `NativeGammaCenteredDerivative`: `not_nativeC3GreenRepresentationOn` | C |
| C: limite original, filtro não trivial | `NativeGammaConjugateCollisionObstruction`: `NativeCollisionParameter`, `nativeCollisionParameter_filter_neBot`, `nativeSourceLocusMismatch_conjugateCollision_tendsto` | N/C |
| D1: ledger corrigido literal | `NativeGammaCollisionMaterialLedger`: `nativeGammaMaterialLedgerTotal`, `_eq_mismatch` | C |
| D2: cabeça/cauda literal e colisão | Mesmo: `nativeGammaMaterialHeadTailLedgerTotal`, `_eq_mismatch`, `nativeGammaCollision_materialLedgers_eq_Wronskian` | C |
| D1-2: totais não zero, todos C,k,R | Mesmo: `nativeGammaCollision_materialCounterexampleFamily` | C |
| D: reconstrução dos pares originais | Mesmo: `nativeGammaCollision_transportCounterexampleFamily` | C |
| D3: companions centrais não triviais | `NativeGammaCoupledCompletionObstruction`: `nativeCompanion_centerChannels_cancel_nontrivially` | C |
| D3: cancelamento dos Wronskians | Mesmo: `nativeXi_native_centerWronskians_cancel_nontrivially`, `nativeXi_native_centerNormWeightedWronskians_cancel_nontrivially` | C |
| D3: completion indispensável nessa identidade | Mesmo: `nativeXiCompletionFactor_centerWronskian_ne_zero`, `nativeArchimedean_centerCorrection_cancel_nontrivially` | C |
| D4: fonte e ambas as pernas antes do pairing | Mesmo: `nativeCoupledCompletion_originalSource_legs` | C |
| D4: duas entradas e todos os crossings | Mesmo: `nativeCoupledCompletion_source_polarized_product_sum` | N |
| D4: canais TFVD com todas as caudas | `CompletedNativeChiralReturnCompletionSplit`: `companion_channels_eq_bracketTfvd`, `source_pairing_skew_eq_product_green_sum` | R |
| Guardas: readouts não substituem estados | `NativeGammaMixedResolventCapstone`, `NativeGammaObservableTransportCapstone` | R |
| Guardas: 36 pares e quatro setores | `NativeGammaMaterialHeadTailLedger`: `nativeGammaWholePair_camera_fourHeadTails` | R |
| Guardas: no-go vestido e testemunha C9 | `C3GammaCameraTraceObstruction`, `NativeGammaCanonicalExteriorWitness` | R |

## Validação e publicação

Ambiente: `ssh llm`; Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`; Lake 5.0.0-src+8c9756b.
Os cinco alvos fonte e os cinco audits novos passaram com `--wfail`.
Os 43 checks de axiomas e os cinco guards transitivos de tipos E corpos
passaram, com apenas `propext`, `Classical.choice`, `Quot.sound`.
Não há nova instância pública. Dependências privadas são inspecionadas.

Procedimento completo, preservado sem enfraquecimento:

```bash
export PATH=/home/thlinux/.elan/bin:$PATH
lake build --wfail CarrySelfAdjointOperator.NativeGammaCoupledCompletionObstruction
bash scripts/audit_gamma_cauchy_transport.sh .lake/conjugate-collision-audit
```

A campanha integral passou com saída zero, de `2026-10-13T16:44:02Z` a
`2026-10-13T16:59:08Z`: 41 builds Audit --wfail, 41 audits diretos
`lean -E warning`, 405 raízes públicas, inventário, checks de diff,
hashes e auditoria estática. Todos os guards passaram apenas com os três
fundamentos aceitos; maior fechamento transitivo: 7134. A raiz --wfail
passou com 10171 jobs; `scripts/audit.sh` passou com 8903 jobs e
`kernel audit passed`. Os logs completos são arquivados na entrega.
Os logs incrementais preservam erros ordinários de elaboração já corrigidos;
eles não são apresentados como falhas matemáticas nem validações finais.
Hashes de publicação, CI externa e a repetição integral pós-integração
são registrados separadamente no manifesto da entrega. CI sem jobs não
conta como execução Lean.

## Nova fronteira científica

A descrição anterior "anulação global do mismatch aberta" foi DECIDIDA
para a proposição universal literal atual: ela foi refutada por pares
conjugados admissíveis arbitrariamente próximos do centro. A mesma
proposição não pode voltar como hipótese oculta de positividade ou sewing.

Permanece aberta a construção e certificação de um transporte vetorial
conjunto correto, que conserve o acoplamento nativo/completion e registre
explicitamente as diferenças entre charts. O cancelamento central é uma
condição necessária, não a definição nem a existência desse mapa.

Não se afirma igualdade do Gamma atual com o chart vestido de F. Não se
afirma impossibilidade de todo transporte ou teoria, positividade quiral
global, identificação dos clocks, unitária das sementes, completude
Laguerre, suporte infinito ou anulação de todas as parcelas do ledger.
Exteriores nativo/C9, escape global, caudas Laguerre e bordos Jacobi
permanecem objetos distintos. Os teoremas finitos e no-go anteriores são
preservados; a campanha numérica não é premissa destas provas.

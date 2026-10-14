# Construção concreta de respostas físicas e teste do porto nativo

Base: `carry-self-adjoint-operator`, main `6807c7dad752ef0a9596c063411d8301a63b6609`. Execução no servidor `llm`.

**Consegui construir respostas concretas no L² original para a multiplicação geométrica por u. A equação vetorial, o fator de energia, os limites dos dois setores e a preservação dos canais originais foram provados. Essa candidata ainda não é a resposta espectral desejada: o porto de valor completado no centro falha no momento de ordem zero, e trocar apenas o operador mantendo esse porto não corrige a falha.**

O resultado é uma tentativa construída e verificada, com uma obstrução específica. Não é uma construção incondicional do operador nativo das alturas, nem uma impossibilidade da teoria ou de outros portos físicos.

## 1. A fonte vem antes do inverso

Seja `H = L²([0,1],du;ℂ)` o carrier físico existente. O avanço geométrico é `M_u f(u)=u f(u)`, com `0≤M_u≤I`. Não foi identificado com o operador de alturas.

Para a característica completada original `F`, o porto positivo existente é `E₊=-F′+iF`. Nas amostras `ζ_(k,j)=(j+1)i/(k+1)`, o canal físico de valor já definido no repositório tem o representante

$$V_{k,c,r}(u)=\sqrt{k+1}\sqrt u\sum_j c_jr^{j+1}\frac{F(\zeta_{k,j})}{E_+(\zeta_{k,j})}u^j.$$

O companheiro completo substitui `F` por `-F′` no numerador. Sua decomposição existente em companheiro nativo e companheiro da compleção foi mantida. Os coeficientes, raios, fatores e a amplitude `√(k+1)` são os originais.

A variável `ζ` amostra a fonte. A variável `z` abaixo é o parâmetro complexo da resposta; elas têm papéis distintos.

## 2. Inverso e resposta construídos no espaço físico

Para `|z|<1`, defini diretamente

$$R(z)f(u)=\frac{f(u)}{1-z^2u},\qquad X_v(z)=R(z)v.$$

O denominador é não nulo em todo `[0,1]`. Foram provados ambos os inversos e a cota

$$(I-z^2M_u)R(z)=R(z)(I-z^2M_u)=I,\qquad \|R(z)\|\le\frac1{1-|z|^2}.$$

Em particular,

$$\boxed{X_v(z)-z^2M_uX_v(z)=v.}$$

A fonte `v` é fornecida antes de aplicar `R`; não é definida pela inversão de uma resposta, por um Gram desejado ou por uma tabela de alturas. A definição `diskCompletedSourceResponse` aplica esse mesmo operador a cada um dos três canais originais: valor, companheiro nativo e companheiro da compleção.

Para o valor, a resposta é explicitamente

$$X^{\rm valor}_{k,c,r}(z;u)=\frac{V_{k,c,r}(u)}{1-z^2u}.$$

As outras duas parcelas têm o mesmo denominador e conservam seus próprios numeradores originais.

## 3. Setor de energia e kernel próprio da resposta

Construí `Bf(u)=√u f(u)` no mesmo L² e provei

$$B^*=B,\qquad B^2=M_u,\qquad \langle M_ux,y\rangle=\langle Bx,By\rangle.$$

O estado de paridade concreto é

$$\mathcal Z_v(z)=\bigl(X_v(z),\ zBX_v(z)\bigr).$$

Seu Gram realiza exatamente o kernel do seu próprio readout cíclico:

$$\frac{w\langle v,X_v(w)\rangle-\overline{z\langle v,X_v(z)\rangle}}{w-\bar z}
=\langle X_v(z),X_v(w)\rangle+\bar zw\langle BX_v(z),BX_v(w)\rangle.$$

A equação vetorial e a igualdade de energia aqui são teoremas da construção, não premissas de um novo certificado. A igualdade desse readout com o Weyl nativo não foi inserida.

Os setores de paridade espectral `(X,zBX)` não foram identificados com as orientações quirais incident/returned. A separação entre esses objetos continua explícita.

## 4. Cauda e limites construídos em todas as ordens

Os aproximantes conservam a mesma fonte:

$$P_m(z)v=\sum_{n=0}^m z^{2n}M_u^nv.$$

O resíduo é o vetor exato

$$P_m(z)v-z^2M_uP_m(z)v-v=-z^{2m+2}M_u^{m+1}v.$$

Também provei

$$\boxed{\|X_v(z)-P_m(z)v\|\le\frac{|z|^{2m+2}}{1-|z|^2}\,\|v\|.}$$

Isso prova `P_m(z)v→X_v(z)` e `BP_m(z)v→BX_v(z)` no L². Não há um resto numérico desconhecido nessa série geométrica do operador físico: o limite é provado para todo `v` e todo `|z|<1`.

**Qual limite foi fechado:** `m→∞` é a ordem do aproximante do resolvente, com a fonte fixa. Isso não afirma convergência quando também variam a malha radial `k`, o cutoff da fonte ou seus coeficientes. Não é uma cota para a cauda desconhecida do Jacobi de `momentos`.

## 5. A fonte completa e seus cruzamentos permanecem presentes

Usando a síntese original, a linearidade do inverso dá

$$R(z)\,\mathrm{incident}
=R(z)C_{\rm nativo}+R(z)C_{\rm complecao}+iR(z)V,$$

$$R(z)\,\mathrm{returned}
=R(z)C_{\rm nativo}+R(z)C_{\rm complecao}-iR(z)V.$$

Essas identidades conservam as hipóteses de regularidade da fonte existente. Não foi substituída a energia assinada por uma soma positiva.

O teorema `diskCompletedSourceResponse_nine_crossings_tendsto` conserva os nove cruzamentos ordenados dos três canais, com fontes e parâmetros independentes e duas ordens de aproximação independentes. Primeiro os vetores completos convergem; depois é aplicado o pairing.

## 6. A resposta pertence ao fecho Cauchy e admite o dicionário existente

Provei que `M_u` preserva o fecho Cauchy já construído. Todos os aproximantes `P_m(z)v` permanecem nele, e o limite `X_v(z)` também permanece quando a fonte está nesse fecho.

Assim `diskCauchyResponse` é uma resposta efetivamente construída no carrier físico fechado. A isometria Cauchy–Laguerre existente pode ser aplicada a ela, e suas coordenadas são os funcionais `laguerreMode` antigos.

Não foi necessária completude Laguerre em todo o L². O setor de energia converge no L² original; não foi acrescentado aqui um teorema de que ele pertence ao fecho Cauchy ou uma transformação Laguerre sobre o espaço inteiro.

## 7. O defeito nativo que não desapareceu por definição

Para a resposta agora construída, resta o escalar explicitamente calculável

$$\delta_v(z)=F'(z)+2z\langle v,X_v(z)\rangle F(z).$$

O novo teorema `diskPhysicalResponse_native_kernel_defect` especializa a identidade anterior ao operador e ao fator de energia concretos. O resíduo da equação vetorial já é zero. A diferença para o kernel original é exatamente

$$K_F(z,w)-\langle\mathcal Z_v(z),\mathcal Z_v(w)\rangle
=\frac{-\delta_v(w)/F(w)+\overline{\delta_v(z)/F(z)}}{2(w-\bar z)}.$$

Valem as exclusões explícitas `F(z)F(w)≠0` e `w≠conj z`. Não foi assumido `δ_v=0`.

## 8. Reprovação exata do porto direto no centro

O porto de valor completado no centro, usando a coluna física original, é

$$v_{\rm valor}=\frac{F(0)}{E_+(0)}\psi_0=-i\psi_0,\qquad \psi_0(u)=\sqrt u.$$

O repositório já prova `E₊(0)=iF(0)` e `F(0)≠0`. Portanto não se trata de escolher uma amplitude nova. O construtor devolve `X_v(0)=v`, e

$$\langle v_{\rm valor},X_{v_{\rm valor}}(0)\rangle=\|v_{\rm valor}\|^2=\frac12.$$

Esse é o porto pontual avaliado no centro sobre a coluna original `ψ₀`. Ele não foi declarado como o limite em `k` das fontes radiais com fator `√(k+1)`.

O momento nativo satisfaz `h₀<1/16`. A desigualdade foi certificada no Lean para essa resposta concreta. Para o incidente radial literal de profundidade `k`, o valor é `(k+1)/2`; seus momentos físicos são `(k+1)/(n+2)`, como registra o readout exato dos aproximantes.

Há uma obstrução ainda mais específica: **mantendo esse mesmo porto de valor, mudar apenas o operador não pode corrigir a ordem zero.** Para quaisquer vetores `x,jx` de um grafo candidato, a equação `x-0²jx=v` força `x=v`. O teorema `centeredCompletedValueSource_not_native_cyclic_response` exclui então o readout canônico com esse porto, sem exigir que o operador seja limitado.

Esse no-go é sobre o porto direto `F(0)/E₊(0)·ψ₀` como fonte cíclica, não sobre todos os portos físicos, os jets enriquecidos ou a teoria. Também não afirma `δ_v(0)≠0`: esse resíduo contém um fator de altura e pode se anular trivialmente no centro. O teste sensível aqui é o valor removível do readout cíclico, que deveria ser `h₀`.

## 9. Resultado e obrigação que permanece

**Construído e provado:** inverso físico complexo no disco, respostas às parcelas completas originais, equação exata, fator de energia, aproximantes com cauda geométrica, limites dos dois setores, retenção das orientações e dos nove cruzamentos, permanência no fecho Cauchy e observações Laguerre.

**Ainda não construído:** o porto espectral obtido da geometria completada cuja energia reproduza a sequência nativa, e o operador/retorno compatível com ele. O porto não pode ser simplesmente o valor zeroth-order acima. É preciso derivá-lo dos jets e do retorno da fonte, com os termos de compleção e os cruzamentos que produzem o readout assinado, antes de provar a realização positiva do kernel inteiro. Multiplicar a fonte por uma constante escolhida para acertar `h₀` não demonstraria os outros momentos ou o kernel de duas variáveis e não foi feito.

A resposta espectral nativa desejada continua aberta. A tentativa presente entrega uma construção física concreta e mostra precisamente por que essa primeira candidata não pode ser apresentada como a realização das alturas.

## Verificação

O módulo `NativePhysicalSourceResponses` tem 44 declarações públicas: 11 definições e 33 teoremas. As provas são exatas; não foi feita uma nova campanha numérica de alturas. O audit cobre os tipos, corpos e dependências de todas as declarações. Os logs e hashes desta entrega estão em `audit/physical-source-responses/`.

O build focado com `--wfail` e a execução direta com `-E warning` passaram. O guard percorreu 6.399 constantes e aceitou apenas `propext`, `Classical.choice`, `Quot.sound`. O registro Cauchy–Laguerre agora cobre 169 declarações em nove módulos.

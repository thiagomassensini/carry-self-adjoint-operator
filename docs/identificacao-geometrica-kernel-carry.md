# Identificação geométrica do par e da medida do kernel carry

**Data:** 4 de setembro de 2026. **Execução:** servidor `llm`.
**Ponto de partida Lean:** `b01bf33f5ab78a02ebb8e48e74af2048b58e1637`.
**Provas novas:** [commit c425018](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/c42501803e88f2af8516f2dee87a891b42eddcc3).

Construímos pares geométricos infinitos com fonte em $\ell^2$, operador positivo limitado e independência de todas as potências. Seus kernels são explícitos. **Ainda não identificamos nenhum deles com o kernel dos momentos nativos.** A investigação agora localiza a diferença no observável e no readout completado, incluindo seus pesos espectrais.

O resultado adicional mais útil é uma condição sobre a medida: para um átomo isolado em $\lambda>0$, de massa $w$, a identidade com $-F'/2F$ exige

$$
\boxed{\quad w=\operatorname{ord}_{1/\sqrt\lambda}(F)\,\lambda.\quad}
$$

Essa condição não é necessária para todo kernel positivo. Ela é necessária para que esse kernel particular seja o readout de uma característica holomorfa como a nativa. Abaixo estão a construção, os testes, a derivação dessa condição e seu alcance.

## 1. Um par diretamente do relógio e da massa crítica

No corte material $2\le n\le M$, use o relógio geométrico $L_n=\log n$ e a massa quadrática de carry $1/n$:

$$
B_M(t)=\sum_{n=2}^M\frac{1/n}{t-\log n}.
$$

A parte ímpar negativa satisfaz, exatamente,

$$
\frac{B_M(-t)-B_M(t)}2
=t\sum_{n=2}^M
\frac{1/(n\log^2 n)}{1-t^2/\log^2 n}.
$$

Isso fornece uma origem concreta para o par

$$
H=\ell^2(\{n\ge2\}),\qquad
(Sx)_n=\frac{x_n}{\log n},\qquad
u_n=\frac1{\sqrt n\log n}.
$$

O fator adicional $1/\log n$ da fonte vem da diferença dos resolventes. A amplitude crítica continua sendo $n^{-1/2}$. A escolha dessa parte ímpar é uma construção examinada nesta rodada; ainda precisa ser ligada ao readout completado das câmeras.

Temos

$$
\|S\|=\frac1{\log2},\qquad
\|u\|^2=\sum_{n=2}^{\infty}\frac1{n\log^2n}<\infty.
$$

As parcelas $B_M(t)$ isoladas divergem; a diferença acima converge localmente uniformemente para $|t|<\log2$. Seu readout é

$$
a_{\rm log}(t)
=t\sum_{n=2}^{\infty}\frac1{n(\log^2n-t^2)}.
$$

A fonte vetorial e o kernel resultantes são completamente explícitos:

$$
\Psi_{\rm log}(t)_n=
\left(
\frac{\log n}{\sqrt n(\log^2n-t^2)},
\frac{t}{\sqrt n(\log^2n-t^2)}
\right),
$$

$$
K_{\rm log}(x,z)=
\sum_{n=2}^{\infty}
\frac{\log^2n+xz}
 {n(\log^2n-x^2)(\log^2n-z^2)}
=\langle\Psi_{\rm log}(x),\Psi_{\rm log}(z)\rangle.
$$

Para $x,z$ reais, com $|x|,|z|<\log2$,

$$
K_{\rm log}(x,z)=
\begin{cases}
\dfrac{a_{\rm log}(z)-a_{\rm log}(x)}{z-x},&x\ne z,\\[4pt]
a_{\rm log}'(x),&x=z.
\end{cases}
$$

Os momentos são

$$
m_k^{\rm log}=\sum_{n=2}^{\infty}\frac1{n(\log n)^{2k+2}}.
$$

Se $P(S)u=0$, então $P(1/\log n)=0$ para infinitos valores distintos. Portanto $P=0$: as potências são linearmente independentes. O mesmo argumento nas potências pares e ímpares dá os Grams ordinário e deslocado estritamente positivos em toda ordem.

**Status:** construção e prova escritas nesta investigação. O mecanismo geral do kernel, incluindo diagonal e Grams, já está formalizado; a instanciação deste par diagonal infinito ainda não foi adicionada ao Lean.

## 2. A versão por fibras de potências primas

Preservando explicitamente a profundidade $k\ge1$ de cada primo $p$, temos outro par:

$$
H_{\rm pp}=\ell^2\{(p,k):p\text{ primo},\ k\ge1\},\qquad
S_{p,k}=\frac1{\log p},\qquad
u_{p,k}=\frac{p^{-k/2}}{\log p}.
$$

A soma geométrica da massa de carry fornece

$$
m_j^{\rm pp}
=\sum_p\frac1{(p-1)(\log p)^{2j+2}},\qquad
a_{\rm pp}(t)=t\sum_p\frac1{(p-1)(\log^2p-t^2)}.
$$

A fonte pertence a $\ell^2$, por comparação com
$2\sum_{n\ge2}1/(n\log^2n)$; $S$ é positivo, simétrico e limitado por $1/\log2$.
A independência de todas as potências segue avaliando uma relação polinomial nas coordenadas $(p,1)$.

A degenerescência em $k$ não destrói essa independência. Contudo, a órbita ocupa somente um raio geométrico por primo; não é densa no Hilbert inteiro. Nesse Hilbert, $S$ não é compacto, pois cada autovalor $1/\log p$ tem multiplicidade infinita. Sua restrição ao subespaço dos raios é compacta.

As medidas concretas desses dois pares, na variável $\lambda=S^2$, são

$$
\rho_{\rm log}
=\sum_{n\ge2}\frac1{n\log^2n}\,\delta_{1/\log^2n},
\qquad
\rho_{\rm pp}
=\sum_p\frac1{(p-1)\log^2p}\,\delta_{1/\log^2p}.
$$

São medidas positivas genuínas. O problema é identificá-las com a medida do readout nativo.

## 3. Por que esses dois readouts não são o nativo

Para uma parcela atômica de massa $w$ em $\lambda>0$,

$$
a_{\rm atom}(t)=\frac{wt}{1-\lambda t^2}.
$$

Em $t_0=1/\sqrt\lambda$, seu resíduo é $-w/(2\lambda)$. Se
$F(t)=(t-t_0)^N g(t)$, com $g(t_0)\ne0$ e $g$ holomorfa, então

$$
-\frac{F'(t)}{2F(t)}
=-\frac{N}{2(t-t_0)}-\frac{g'(t)}{2g(t)}.
$$

A igualdade dos readouts exige $w/\lambda=N$, um inteiro positivo.
O argumento usa um átomo isolado e um resto holomorfo; não se aplica a uma medida arbitrária sem essas condições.

Nos dois pares construídos,

$$
\frac{w_n}{\lambda_n}=\frac1n,\qquad
\frac{w_p}{\lambda_p}=\frac1{p-1}.
$$

Essas razões não são multiplicidades inteiras. As séries convergem localmente uniformemente fora de seus polos, que não têm acumulação finita. Uma igualdade de germes com o readout nativo se prolongaria meromorficamente no domínio conexo relevante e teria de respeitar os resíduos.

Mesmo uma mudança global $u\mapsto cu$, $S\mapsto\beta S$, com $c,\beta>0$, não corrige essa família: as razões tornam-se
$c^2/(\beta^2 n)$ ou $c^2/(\beta^2(p-1))$. Para índices suficientemente grandes, ficam estritamente entre 0 e 1.

Isso é uma incompatibilidade **desses pares e dessas mudanças globais** com o readout holomorfo nativo. Seus kernels positivos continuam válidos. Outros observáveis, pesos, fontes e acoplamentos de retorno não foram excluídos.

A analiticidade necessária já está disponível no repositório:
`completedNativeOperatorCharacteristic_analyticAt`, em `GlobalKernelProbe.lean`.
Todo o eixo real pertence ao domínio de alturas. Não é preciso pressupor uma extensão inteira global para usar o argumento nesse domínio.

A condição também explica a importância de manter as multiplicidades nas compressões geométricas.

## 4. O que a compressão Naimark preserva

Na fibra finita de um número material $m$, sejam $v_p=v_p(m)$ e

$$
(A_mx)_p=\frac1{\sqrt{v_p}}\sum_{k=1}^{v_p}x_{p,k}.
$$

O mapa satisfaz $A_mA_m^*=I$ e entrelaça os relógios diagonais. Para
$S_m=\operatorname{diag}(1/\log p)$ e $\nu_{p,k}=1/\log p$,

$$
\langle\nu,S_m^{2j}\nu\rangle
=\operatorname{Tr}(S_m^{2j+2})
=\sum_{p\mid m}\frac{v_p}{(\log p)^{2j+2}}.
$$

A fonte comprimida é

$$
(A_m\nu)_p=\frac{\sqrt{v_p}}{\log p}.
$$

Esse fator $\sqrt{v_p}$ preserva todos os momentos e o kernel. Trocar a fonte comprimida por $1/\log p$, ou trocar um traço ponderado pelo traço ordinário, perde a multiplicidade.

O determinante mostra o mesmo dado:

$$
\det(I-t^2S_m^2)
=\det(I-t^2\bar S_m^2)
\prod_{p\mid m}
\left(1-\frac{t^2}{(\log p)^2}\right)^{v_p-1}.
$$

O produto adicional corresponde ao setor $\ker A_m$. Podemos preservar esse setor ou conservar suas multiplicidades no readout; não é obrigatório manter fisicamente todas as coordenadas redundantes.

Na fibra $m=12$, essas identidades foram verificadas simbolicamente. A fatoração aritmética e o mapa de médias vêm das fontes anteriores, sem usar os momentos nativos. A identidade vetor–traço foi explicitada nesta investigação.

## 4.1 Uma nova construção que satisfaz as multiplicidades

Usamos a condição acima para propor e testar uma correção geométrica explícita.
Em cada fibra prima, tome o vetor já construído
$v_p=(p^{-k/2}/\log p)_{k\ge1}$ e forme

$$
V_{\rm fibra}=\bigoplus_p |v_p\rangle\langle v_p|,
\qquad S_{\rm fibra}=\sqrt{V_{\rm fibra}},
\qquad u=\bigoplus_p v_p.
$$

Agora o autovalor positivo de cada fibra é sua própria energia:

$$
\lambda_p=\|v_p\|^2=\frac1{(p-1)\log^2p}.
$$

A massa da fonte nesse autovalor também é $\lambda_p$. Logo

$$
m_j=\sum_p\lambda_p^{j+1}=\operatorname{Tr}(V_{\rm fibra}^{j+1}),
\qquad
F_{\rm fibra}(t)=\prod_p(1-t^2\lambda_p),
\qquad
a_{\rm fibra}(t)=-\frac{F_{\rm fibra}'(t)}{2F_{\rm fibra}(t)}.
$$

Como $\sum_p\lambda_p<\infty$, temos um operador de classe traço e uma
característica inteira. Seus zeros geométricos são
$\pm\sqrt{p-1}\log p$, com multiplicidade 1. O operador foi alterado
concretamente: passou a acoplar as profundidades de cada fibra. Nenhum momento
nativo entrou nessa definição.

A versão por números materiais é
$\lambda_n=1/(n\log^2n)$, $S_n=\sqrt{\lambda_n}$, $u_n=\sqrt{\lambda_n}$.
Ela também satisfaz a relação massa/autovalor igual a 1.

**As duas construções corrigem o defeito de multiplicidade, mas ainda não
identificam os momentos nativos**, conforme os testes abaixo. São novas
candidatas propostas e analisadas nesta rodada; não foram localizadas como
construções completas já formalizadas nas fontes anteriores.

## 5. Comparações com a mesma referência nativa

Para
$F(t)=\sum f_jt^{2j}$, calculamos os momentos nativos pela recorrência

$$
f_0h_n+\sum_{k<n}h_kf_{n-k}+(n+1)f_{n+1}=0.
$$

Os $f_j$ foram obtidos pelas integrais theta da representação já demonstrada para a característica nativa. Não entraram zeros tabelados, autovalores desejados ou ajustes espectrais na construção dos candidatos.

A referência inclui 80 momentos a 500 dígitos de trabalho, extraídos do cache theta a 1600 dígitos. Recalculamos independentemente $h_0,\ldots,h_{15}$, usando outra coordenada de integração a 90 e 150 dígitos. As concordâncias mínimas foram, respectivamente, 87 e 147 casas relativas. Isso é reprodução numérica de alta precisão, sem aritmética intervalar.

Para separar a forma de uma eventual mudança global de massa ou escala, usamos

$$
I_j=\frac{m_jm_0^{\,j-1}}{m_1^j}.
$$

Esses números não mudam sob $u\mapsto cu$, $S\mapsto\beta S$.

| Construção | $I_2$ | $I_3$ |
|---|---:|---:|
| **Referência nativa** | **2.410719741809124** | **6.890919499842071** |
| Relógio material com massa $1/n$ | 1.532855110882804 | 2.540674393339241 |
| Fibras primas com massa $p^{-k}$ | 1.134526 a 1.160372 | 1.333414 a 1.394837 |
| Novo Gram de posto um por fibra prima | 1.215748 a 1.243403 | 1.518694 a 1.588571 |
| Novo Gram por número material | 1.716953683418 | 3.119980337582 |
| Torre $S_j=1/j$, $u_j=1/j$ | $10/7$ | $15/7$ |
| TFVD C3, $V=A_q^*A_q$, $u_k=q^k$ | $21/8$ | $321/32$ |
| Green/síntese C5, fonte $\delta_1$ | 2.430555555555556 | 7.262731481481481 |
| Modo misto 3–4–6 compactado | 1.2323443314 | 1.6469248587 |
| Traço dos seis modos das câmeras | 1.4256626077 | 2.4180939215 |

A faixa das fibras primas combina a soma até $10^7$ — 664.579 primos — com uma cota analítica da cauda por todos os inteiros. As somas finitas usam ponto flutuante; a faixa não foi certificada por Lean nem por arredondamento intervalar.

No TFVD, $q=b^{-1/2}$ e $A_q=q^{-1}(I-qU)^2$. A análise conserva os termos de bordo. Para a fonte real de retorno $u_k=q^k$, obtivemos exatamente

$$
m_0=\frac b{b-1},\qquad m_1=b+1,\qquad
m_2=(b+1)(b+4),\qquad I_2=\frac{b(b+4)}{b^2-1}.
$$

A análise TFVD, sua síntese inversa, Green, fontes dos dois canais de retorno e medidas compactas foram avaliados em **525 registros**, nos graus 0–12: 504 avaliações nos cortes 64, 128, 256 e 512, mais 18 modelos de profundidade e três medidas compactas. Esse número inclui cortes repetidos e apresentações equivalentes; não representa 525 construções independentes. Três casos foram repetidos a 90 dígitos. As diferenças relativas dos momentos entre cortes 128 e 256 ficaram abaixo de $10^{-61}$ nesses casos, enquanto as diferenças para o alvo persistiram.

O quase acerto C5 é ilustrativo: depois de ajustar diagnosticamente as duas primeiras ordens, os próximos desvios são $+0.823\%$, $+5.40\%$ e $+14.08\%$. Não é uma identificação.

## 6. Retorno, all-bases e bordo também foram testados

A investigação não ficou restrita aos operadores diagonais.

- A coligação real reproduziu a identidade polarizada
  $(\bar w-z)S(z)G_ES(w)^*=B(z)-B(w)^*$, com resíduo máximo observado de $2.88\cdot10^{-13}$.
- Da medida Green all-bases extraímos o novo candidato
  $V_G=\mathcal F^{-1/2}B^*B\mathcal F^{-1/2}$,
  $\mathcal F=E^*E+B^*B$.
  Foram testadas sementes materiais e suas imagens na métrica, até o corte 256.
- Da válvula C2 extraímos $V=B_{C2}^*B_{C2}$. Oito momentos de quatro sementes foram calculados exatamente, com suporte que não alcança o bordo do corte.
- O testemunho de proveniência foi reparado juntando as duas leituras $(Q,A)$, preservando exatamente a informação que $Q$ sozinho perdia.

Nenhuma dessas fontes selecionadas reproduziu os invariantes nativos. Para os candidatos all-bases, não demonstramos uma cota uniforme de convergência dos momentos; seus resultados finitos não são uma exclusão de todos os limites possíveis.

Cinco rotinas autocontidas dos grafos antigos reproduziram os resultados históricos, além das identidades algébricas adicionais. Os pipelines históricos completos ainda dependem de arquivos ausentes; isso está registrado separadamente. Os rótulos antigos de gates foram tratados como resultados daquele inventário, sem transformá-los em proibições universais.

## 7. A condição de multiplicidades agora está no Lean

Esta rodada acrescentou dois módulos, com **nove teoremas públicos**:

| Módulo | Conteúdo demonstrado |
|---|---|
| [AtomicLogDerivativeResidue.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/c42501803e88f2af8516f2dee87a891b42eddcc3/CarrySelfAdjointOperator/AtomicLogDerivativeResidue.lean#L117) | Resíduo de uma função analítica de ordem finita; resíduo de um átomo de resolvente com resto contínuo; igualdade local de readouts implica $w/\lambda=\operatorname{analyticOrderNatAt}(F,t_0)$. |
| [CompletedNativeAtomicMultiplicity.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/c42501803e88f2af8516f2dee87a891b42eddcc3/CarrySelfAdjointOperator/CompletedNativeAtomicMultiplicity.lean#L90) | Coeficiente do polo da Weyl nativa, transporte para a coordenada recíproca quadrada e fórmula exata da massa escalar já definida na API. |

O segundo módulo prova, para um zero real $z_0$ no domínio nativo,

$$
\boxed{
\mathrm{positiveJacobiAtomicCyclicMass}(z_0)=
\frac{\operatorname{analyticOrderNatAt}(F,z_0)}
 {(\operatorname{Re}z_0)^2}.
}
$$

Essa igualdade **dispensa um certificado Hilbert**: identifica a massa
escalar definida pelo resíduo. A realização dessa massa como medida/vetor
espectral continua dependendo da construção positiva correspondente.

As provas locais e a identificação escalar nativa estão verificadas pelo
kernel Lean. A convergência das novas séries geométricas, a aplicação global
da condição a todos os seus polos e os novos pares infinitos continuam como
derivações escritas nesta rodada, sem instanciação Lean completa.

A auditoria completa `scripts/audit.sh` terminou com sucesso: 14 chamadas
de build, nenhum erro ou aviso e os nove teoremas novos com apenas
`propext`, `Classical.choice` e `Quot.sound`. A auditoria do conjunto de
kernels agora inclui 77 declarações.

## 8. O que falta demonstrar para o par correto

O Lean já dispõe da ponte exata. Para um par geométrico concreto, é preciso provar

$$
D_n(S,u)=f_0\|S^nu\|^2+
\sum_{k<n}f_{n-k}\|S^ku\|^2+
(n+1)f_{n+1}=0
\qquad\text{para todo }n.
$$

Isso identifica a sequência pela unicidade da recorrência. Junto com a independência das potências, entrega o certificado nativo. Nos pares logarítmicos desta investigação, a independência foi demonstrada em papel; o readout é que não coincide.

Os primeiros dados necessários para um observável $V=S^2$ correto são

$$
\|u\|^2=0.0231049931154189707889\ldots,
$$

$$
\langle e_0,Ve_0\rangle=0.0016088556745971409753\ldots,
\qquad
\|Ve_0-\langle e_0,Ve_0\rangle e_0\|
=0.0019108977920880258769\ldots,
$$

onde $e_0=u/\|u\|$. São restrições extraídas do alvo para comparação; a matriz de Jacobi formada delas não foi apresentada como construção geométrica independente.

A direção que esta rodada sustenta é: **derivar o observável e a fonte depois da conexão completa entre câmeras, retorno e completação, mantendo as multiplicidades no readout**. A origem do peso $b^{-k/2}$ já está estabelecida. A nova condição relaciona esse peso com os autovalores do observável e com as multiplicidades que a característica exige.

Não foi demonstrado que essa ligação completa seja impossível, nem que precise ser postulada. As construções explícitas acima dizem quais escolhas já falham e quais dados a próxima identidade deve conservar.

## 9. Arquivos para continuar

Pasta de trabalho no servidor:
`/home/thlinux/carry-kernel-geometric-search-20260904/`.

Os diretórios contêm:

- `reference/`: momentos nativos, validação independente e restrições da matriz cíclica.
- `candidates/`: 525 avaliações TFVD/Green/medidas, comparação e validação multiprecisão.
- `graph/`: fontes preservadas, grafos, reparação de proveniência, relógio, all-bases e cálculos C2 exatos.
- `fredholm/`: fibras primas, identidades de compressão, somas e condições dos resíduos.
- `source/`: script nativo e cache theta preservados.
- `dossiers/`: três investigações detalhadas com arquivos, declarações e limites de cada resultado.
- `manifest.json`: hashes dos artefatos desta entrega.

Leituras diretas:

- [Operadores, grafos e retorno](../research/geometric-kernel-search-2026-09-04/dossiers/carry-geometric-graph-investigation.md).
- [Famílias TFVD, Green e medidas compactas](../research/geometric-kernel-search-2026-09-04/dossiers/carry-geometric-candidates.md).
- [Fibras, Naimark e traços](../research/geometric-kernel-search-2026-09-04/dossiers/carry-geometric-fredholm-investigation.md).
- [Condição atômica e novo Gram por fibra](../research/geometric-kernel-search-2026-09-04/dossiers/carry-geometric-atomic-residue-supplement.md).
- [Referência nativa](../research/geometric-kernel-search-2026-09-04/reference/native_moments.json) e [validação independente](../research/geometric-kernel-search-2026-09-04/reference/quadrature_validation.json).
- [Auditoria Lean completa](../research/geometric-kernel-search-2026-09-04/full_lean_audit.log).

Reprodução da referência, sem modificar o cache original:

~~~bash
cd /home/thlinux/carry-kernel-geometric-search-20260904
python3 build_reference.py
OPENBLAS_NUM_THREADS=1 python3 validate_reference.py
python3 target_constraints.py
~~~

As rotinas de candidatos conservam os momentos brutos e marcam explicitamente qualquer normalização usada apenas para comparação. Os comandos detalhados de cada laboratório estão nos dossiês.

**Estado da obrigação principal:** aberta. Não tratar as provas dos kernels candidatos, os testes positivos dos Grams ou a nova condição de multiplicidades como prova de $D_n=0$ para o operador nativo.

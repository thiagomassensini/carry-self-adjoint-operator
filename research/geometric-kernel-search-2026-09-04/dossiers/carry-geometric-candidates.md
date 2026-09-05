# Candidatos geométricos positivos: retorno carry, Green e medidas compactas

> Relatório de uma subinvestigação. Consulte o [estado consolidado da entrega](../README.md) para a integração dos dois novos módulos Lean, a auditoria final e a obrigação que continua aberta.

Investigação de2026-09-04 no servidor `llm`, com arquivos novos somente em `/home/thlinux/carry-kernel-geometric-search-20260904/candidates`. Nenhum Lean, Git ou script original foi alterado. Máximo12processos na varredura e3processos na validação multiprecisão; variáveis BLAS/OMP/MKL/NumExpr fixadas em1.

## Resultado

Os candidatos determinados diretamente pelas peças finitas/verticais examinadas **não identificaram os momentos nativos**. Isso foi verificado em ordens0–12, quatro cutoffs e, para três candidatos relevantes, com90dígitos. As discrepâncias que persistem depois de remover diagnosticamente massa e escala são muito maiores que a variação de cutoff observada. Trata-se de incompatibilidades dessas escolhas de observável e fonte; não é uma obstrução a toda a geometria carry nem um teorema Lean sobre o alvo.

A comparação mais instrutiva é a análise completa `V=Aq* Aq`, com o **modo real de retorno** `u_n=q^n`. Ela conserva os traces e não reutiliza o estado C3 ortogonal anteriormente refutado. Ainda assim, seus três primeiros momentos têm uma fórmula exata diferente do alvo, mesmo permitindo somente uma mudança de massa e escala:

$$
m_0=\frac b{b-1},\quad m_1=b+1,\quad m_2=(b+1)(b+4),\qquad
\frac{m_0m_2}{m_1^2}=\frac{b(b+4)}{b^2-1},\quad q=b^{-1/2}.
$$

Em b=3, o invariante é21/8=2.625. O valor da referência nativa fornecida pelo coordenador é2.41071974180912414432394129713. A fórmula do candidato foi também reconstruída com aritmética racional exata até ordem12.

## Objetos e proveniência

O alvo numérico é `reference/native_moments.json`, gerado pelo coordenador desta rodada, contendo h e f. Não usei raízes, zeros ou a Jacobi formada de h para construir qualquer candidato. A validação independente da referência por quadratura está a cargo do coordenador; esta análise consome seus bytes sem elevar números a prova formal.

As construções fixas usam:

- `q=1/sqrt(b)` nas bases2,3,4,5,6,7.
- `Aq=q^-1(I-qU)^2=q^-1 I-2U+qU²`, a análise completa da nota `TFVD_PRIMOS_HILBERT_COVARIANT_MASS_GAP_EXTENDED/DERIVACOES_ANALITICAS.md:18–31,155–194`, agora também representada por `CarryTfvdTraceMetricKernel.lean`.
- `Kq=Aq^-1=q(I-qU)^-2`, a síntese causal da mesma nota, linhas34–50.
- `Gq=U Kq`, o Green de kernel `r q^r`, exatamente a série `carryWeightedVerticalGreenKernel`/`carryWeightedVerticalGreen` de CPFormal. Como U é uma isometria no Hilbert infinito, `Gq*Gq=Kq*Kq`: estas duas apresentações não contam como duas construções independentes. Os hard walls finitos diferem na última linha, o que foi acompanhado pela variação de cutoff.
- Fontes `delta0`, `delta1`, `q^n`, `n q^n`, `(n+1)q^n`, `(1-n)q^n`. As duas primeiras são coordenadas do reservatório; `q^n` e `nq^n` são literalmente os modos de `CpCarryWeightedVerticalReturn.lean`, e as duas seguintes são suas combinações com coeficientes±1, sem ajuste ao alvo.
- Uma fonte exploratória adicional, `q^n log(n+2)`, registrada como `depth_log_modulation`. **n aqui é a coordenada vertical de profundidade. Essa fonte não é o log-jet em células materiais do estado completado nativo.** Seu nome e status no JSON explicitam essa distinção.

Os observáveis positivos testados são `V=T*T`, T=Aq,Kq,Gq. Na linguagem do novo kernel, o correspondente S é a raiz positiva de V; os cálculos dos momentos e do resolvente usam V diretamente. A positividade de V é a de um adjunto-quadrado geométrico e não a hipótese de positividade dos momentos nativos. Não construí em Lean essa raiz nem aleguei `hcyclic` já provado para esses novos candidatos.

Também foram examinadas medidas compactas source-side:

1. Modo3–4–6, `v=x/6=exp(-xi)`, com os momentos racionais exatos recuperados nas notas.
2. Modo puro uniforme de câmera, `v=x/b`, momentos1/(n+1).
3. Estado traçoI/6 no POVM de seis câmeras: soma dos modos puros3,4(rank2),5,7 e do modo misto(rank1), com observável comum `v=x/7`. Isso é uma escolha explícita de estado traço, sem afirmar que seja o observador da característica completada.
4. Distribuição de profundidade `P(K=k)=(1-1/b)b^-k`, observáveis `b^-k`, `(k+1)^-2` e `log(k+2)^-2`. O primeiro vem diretamente da massa de carry; os inversos são funções exploratórias fixas da profundidade, sem parâmetros extra ajustados. Não se identificam essas variáveis com alturas nativas.

## Como a comparação evita um falso ajuste

Cada registro conserva os momentos brutos `m_n=<u,V^n u>`. Para comparar a forma independentemente de um eventual fator global de fonte e de escala do observável, calculamos

$$
c_n=\frac{m_n/m_0}{(m_1/m_0)^n}.
$$

Multiplicar u por uma constante e V por outra não altera c_n. Essa remoção de massa/escala é **um diagnóstico**, não uma construção com parâmetros fornecidos pelo alvo. O arquivo registra os dois multiplicadores que seriam necessários e os chama `diagnostic_only_*`; eles não foram usados para definir os operadores ou fontes.

Referência nativa:

| Ordem | c_n nativo |
|---:|---:|
|2|2.41071974180912414432394129713|
|3|6.8909194998420713776368142618|
|4|20.7599497558555939870865094423|

Alguns candidatos relevantes:

| Construção | c2 | c3 | c4 | Leitura |
|---|---:|---:|---:|---|
| C3, Aq* Aq, u=q^n |2.625|10.03125|45.462890625|Desvio já na primeira forma invariante, e crescente nas próximas ordens.|
| C5, Kq*Kq, u=delta1 |2.4305555556|7.2627314815|23.6828462577|Quase acerto inicial: +0.823%, depois+5.40%,+14.08%; não é igualdade.|
| C6, Kq*Kq, u=delta1 |2.2040816327|5.9573177843|17.4602848813|Melhor RMSlog de ordens2–12 na varredura, ainda−8.57%,−13.55%,−15.89% nas primeiras três.|
| Modo misto compacto |1.2323443314|1.6469248587|2.3035774217|A mudança de variável resolve o crescimento fatorial, mas a forma dos momentos permanece diferente.|
| Câmera pura compacta |1.3333333333|2|3.2|A família uniforme positiva também não fornece a forma nativa.|
| Traço das seis câmeras |1.4256626077|2.4180939215|4.5734560978|Reter todos os modos desse POVM com estado traço não identifica os momentos.|
| ProfundidadeC2, observável2^-k |1.2857142857|1.8|2.6129032258|Peso quadrático correto com esse observável específico ainda é insuficiente.|

A busca contém525registros, incluindo repetições de cutoff e apresentações equivalentes Green/síntese. Não são525teorias independentes. Não houve otimização sobre parâmetros contínuos.

## Verificação de cutoff e precisão

O código aplica A e seu adjunto pelo stencil; K e seu adjunto por duas recorrências triangulares, evitando inversão densa. Antes da varredura, foram conferidos numericamente `A_N K_N=I`, as identidades de adjunto e a correspondência entre as linhas de Aq e o bracket. Momentos pares foram computados como normas quadradas de potências para reduzir cancelamento artificial.

Cutoffs64,128,256,512, graus0–12:

- Maior diferença relativa observada64→512:2.04×10^-5, entre todos os momentos/operadores/fontes da varredura.
- Em precisão dupla,128e256 coincidem com512 nos momentos registrados. Isso significa estabilidade até a resolução numérica usada, não igualdade matemática.
- Validação com90dígitos, cutoff128→256, erro relativo máximo dos momentos0–12:

| Candidato | Diferença observada |
|---|---:|
| C3 análise, retornoq^n |8.48×10^-62|
| C5 síntese, delta1 |2.58×10^-63|
| C6 síntese, delta1 |1.68×10^-72|

As discrepâncias percentuais em relação ao alvo sobrevivem a essa checagem. Para C3 retorno, m0,m1,m2 e toda a sequência até grau12 foram calculados também por frações exatas. Não se afirma aqui uma cota intervalar do erro da referência nem uma prova Lean da incompatibilidade com h.

## Kernels em dois parâmetros

O arquivo `comparison.json` também compara séries truncadas do kernel par/ímpar em quatro pares `(x,z)` depois da mesma normalização diagnóstica. Registra a diferença entre truncar no grau8e12 e um indicador de pertença ao domínio suficiente de Neumann do candidato. Dois pontos de candidatos extremos ficaram fora dessa cota suficiente; seus números são apenas polinômios truncados, e não foram usados como verificação de kernel resolvente.

Por exemplo, na diagonal normalizada t=0.1, dentro da cota de Neumann para todos os casos desta tabela:

| Candidato | Kernel truncado grau12 | Diferença relativa ao alvo |
|---|---:|---:|
| Referência nativa |1.0312555374864416|—|
| C5 síntese, delta1 |1.0312683423553208|+1.24×10^-5|
| C6 síntese, delta1 |1.0311453751397597|−1.07×10^-4|
| C3 análise, retorno |1.0313870764335107|+1.28×10^-4|
| Misto compacto |1.0306279116800532|−6.09×10^-4|

A pequena discrepância pontual não supera a incompatibilidade de coeficientes: a normalização fixa as duas primeiras ordens e t pequeno suprime as seguintes. Esse é um exemplo concreto de por que não basta comparar visualmente um kernel perto da origem.

## Mecanismos que estes testes esclarecem

1. **Bordo próprio realmente muda a métrica, mas não resolve automaticamente D_n.** A análise Aq inclui exatamente Mq, sem perder os cruzamentos de trace. Sua família de momentos ainda precisa de outro observável/readout para passar o defeito nativo.
2. **Green e síntese não são novos graus de liberdade neste Gram.** `G=U K` implica `G*G=K*K` no infinito. Alterar somente entre essas duas apresentações não pode reparar uma incompatibilidade de momentos que já persiste no limite.
3. **O reservatório afim tem dois canais concretos.** Para `u=q^n(a+nb)`, Aq u tem suporte nas duas primeiras coordenadas. Se depois se escolher um observável diagonal de profundidade sobre o estado de análise Aq u, a órbita fica em no máximo duas coordenadas e não pode fornecer independência em todas as ordens. Isso é uma restrição desse observável diagonal no reservatório; operadores que acoplam o bulk não têm esse mesmo argumento de rank.
4. **Há um caminho independente para hcyclic em alguns operadores bandados.** Para V=Aq*Aq e u=q^n, Vu tem suporte{0,1}; potências subsequentes ganham duas coordenadas e o coeficiente externo não zera. Um argumento do maior índice pode provar ausência de relação polinomial da órbita de V. Para passar à raizS=V^(1/2), uma relação p(S)u=0 produziria a relação par p(-S)p(S)u=0 em V. Esse é um caminho algébrico escrito para a independência, ainda não formalizado nesta rodada. Ele não elimina a incompatibilidade de D_n já detectada.
5. **A próxima variável deve vir do readout completado.** Os testes justificam procurar o transporte entre parâmetro material/altura e observável positivo, incluindo completação, em vez de calibrar a massa e trocar a escala de um desses operadores crus. A fonte das log-potências nativas depende de células materiais; a modulação logarítmica da profundidade testada aqui não a substitui.

## Artefatos e reprodução no servidor

Diretório: `/home/thlinux/carry-kernel-geometric-search-20260904/candidates`.

- `carry_candidates.py` / `carry_candidates.json`: candidatos sem qualquer entrada do alvo;525registros.
- `compare_candidates.py` / `comparison.json` / `comparison.log`: comparação em todas as ordens e cutoffs, invariantes e kernels truncados.
- `validate_candidates_mp.py` / `validation_mp.json`: três candidatos em90dígitos e momentos racionais exatos de retorno nas seis bases.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1 \
  python3 /home/thlinux/carry-kernel-geometric-search-20260904/candidates/carry_candidates.py \
  --output /home/thlinux/carry-kernel-geometric-search-20260904/candidates/carry_candidates.json \
  --workers 12
python3 /home/thlinux/carry-kernel-geometric-search-20260904/candidates/compare_candidates.py
python3 /home/thlinux/carry-kernel-geometric-search-20260904/candidates/validate_candidates_mp.py
```

Hashes SHA256 dos bytes consumidos/produzidos:

| Artefato | SHA256 |
|---|---|
| referência nativa | `e64079c76eef9214449a8cf1d2858b759db6d6a2190d7790a640ccceb9760c9e` |
| carry_candidates.py | `a21b424db7b7eb06e0b2ce4cacfe2be15424d5e1df8d96a780674d239b84f642` |
| carry_candidates.json | `3bbfcaec16643abfee2eec5a41c29d05eea297d75c5453b3967bfa82aa57dcaa` |
| compare_candidates.py | `57e84d68e1c0368f8967de015bf6d5ab07324ba50a106b2625bfb8fd8f27312f` |
| comparison.json | `8d3c2e4a23bb2e5cdcc6e74b630199d4a355125dab2c9cf430033b8f0b2ee3bc` |
| validate_candidates_mp.py | `458193c5ed7c28d651517dd9e5e74cf1da15cf583e801315d69bbb1c856a54c0` |
| validation_mp.json | `9a2c58bfeda3c354f942d17653c7685869a5ea238bc94c770abaf10d0c3166f3` |

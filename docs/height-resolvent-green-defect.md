# Do resolvente de alturas ao kernel Green: estado, resíduos e limite

Estudo de 13/10/2026. Base formal: `carry-self-adjoint-operator` main `a777f9c2b7d1b267a3f30cd4309af5cde9dd539e`. Dados: `momentos` main `a54f267365d5d8c965376734b17b10ae89ed3f74`, no servidor `llm`.

**Resultado novo:** a ponte entre o resolvente quadrático do Jacobi e o kernel Green pode ser escrita como uma identidade exata que retém dois defeitos independentes: o da equação vetorial e o da característica original. A construção usa os dois setores de paridade e fornece uma cota a posteriori. Um critério de limite usa convergência dos estados desses setores; não pede convergência da torre inteira em norma de operador.

Esse resultado organiza uma obrigação concreta de construção. Ele não identifica por hipótese o Gram físico com o canônico, não prova positividade assinada all-order e não certifica a cauda nativa ainda desconhecida.

## 1. O estado que o estudo de `momentos` permite reutilizar

Para uma matriz Jacobi física positiva `J_N`, a campanha calcula

$$\widehat J_N=J_N/s,\quad \widehat R_N(x)=(\widehat J_N-xI)^{-1},\quad q_N(u)=-xh_0\langle e_1,\widehat R_N(x)e_1\rangle,\quad u=1/(sx).$$

Na variável de altura `z`, ponha `u=z²`. Com a fonte natural `v=√h₀e₁`,

$$X_N(z)=(I-z^2J_N)^{-1}v,\qquad q_N(z^2)=\langle v,X_N(z)\rangle.$$

Isso dá a equação `X_N-z²J_NX_N=v`. Nenhuma altura ou peso espectral é necessário como entrada.

Escolha um fator de energia `B_N` com `J_N=B_N*B_N`. Nos testes abaixo ele vem da fatoração LDL/Cholesky da mesma matriz, sem diagonalização. O estado completo é

$$\boxed{\mathcal Z_N(z)=\bigl(X_N(z),\ zB_NX_N(z)\bigr).}$$

Seu Gram é

$$G_N(z,w)=\langle X_N(z),X_N(w)\rangle+\bar z w\langle B_NX_N(z),B_NX_N(w)\rangle.$$

Esses dois setores são a paridade espectral par/ímpar. Eles não foram identificados com as pernas incident/returned da fonte quiral física. A fonte nativa, a compleção e seus cruzamentos continuam sendo dados que o transporte físico precisa conservar.

O primeiro setor contém as potências pares da altura; o segundo contém as ímpares. Na expansão formal `X(z)=Σ z^(2j)J^jv`, os jets são `J^jv` e `BJ^jv`. A fatoração de energia explica os momentos `h_(i+j)` e `h_(i+j+1)`, respectivamente. Esta observação sobre séries não acrescenta aqui uma afirmação de convergência analítica dessa expansão.

No centro, `G_N(0,0)=‖v‖²=h₀`. Essa é a fonte do Jacobi. Não se trata de renormalizar a coluna física Cauchy de norma quadrada `1/2`; sua identificação literal com o jet espectral continua excluída pelo teste de ordem zero anterior.

## 2. Identidade exata com os resíduos visíveis

Trabalhe em espaços de Hilbert complexos `H,K`, com operadores contínuos `J:H→H` e `B:H→K` satisfazendo explicitamente

$$\langle Jx,y\rangle=\langle Bx,By\rangle.$$

Para dois candidatos vetoriais `x=X(z)`, `y=X(w)` e a mesma fonte `v`, defina

$$r_z=x-z^2Jx-v,\quad r_w=y-w^2Jy-v,\quad q_z=\langle v,x\rangle,\quad q_w=\langle v,y\rangle.$$

A característica completada original `F` e sua derivada entram por um segundo resíduo, sem divisão:

$$\delta_z=F'(z)+2zq_zF(z),\qquad \delta_w=F'(w)+2wq_wF(w).$$

O kernel alvo, com a mesma normalização da API de momentos, é

$$K_F(z,w)=\frac{-F'(w)/F(w)+\overline{F'(z)/F(z)}}{2(w-\bar z)}.$$

Para `F(z)F(w)≠0` e `w≠conj z`, a identidade nova é

$$\boxed{K_F(z,w)-G(z,w)=
\frac{\bar z\langle x,r_w\rangle-w\langle r_z,y\rangle}{w-\bar z}
+\frac{-\delta_w/F(w)+\overline{\delta_z/F(z)}}{2(w-\bar z)}.}$$

A primeira parcela conserva os dois crosses ordenados do resíduo vetorial. A segunda mede a identificação com a característica original. Uma não é apagada por boa concordância da outra.

O teorema `weightedReadout_sub_parityGram` fornece antes a identidade **sem dividir por `w-conj z`**. Portanto a álgebra anterior à normalização também fica disponível nos pontos de colisão; não foi afirmada uma extensão removível do kernel dividido nesses pontos.

## 3. A cota que transforma o resíduo em uma obrigação verificável

A identidade dá

$$\begin{aligned}
|K_F-G|\le{}&\frac{|z|\,\|x\|\,\|r_w\|+|w|\,\|r_z\|\,\|y\|}{|w-\bar z|}\\
&+\frac{|\delta_w|/|F(w)|+|\delta_z|/|F(z)|}{2|w-\bar z|}.
\end{aligned}$$

Todos os denominadores permanecem explícitos. A cota não é uniforme perto de um zero de `F` nem perto de `w=conj z` sem estimativas adicionais.

Ela permite uma investigação anterior à hipótese de Gram canônico: construir respostas a partir da fonte completa e controlar `r` e `δ` diretamente. Preservar as respostas completas importa mesmo quando o escalar `q_N` parece estabilizado.

## 4. Um critério de limite mais específico que convergência de operadores

O teorema `characteristicKernel_eq_limit_parityGram` permite que `J_N` e `B_N` variem em espaços de Hilbert comuns. Suas hipóteses são:

- a igualdade de energia em cada ordem;
- convergência em norma de `X_N(z)`, `X_N(w)`, `B_NX_N(z)` e `B_NX_N(w)`;
- `r_N(z),r_N(w)→0` e `δ_N(z),δ_N(w)→0`;
- regularidade dos dois valores de `F` e separação dos parâmetros.

A conclusão é que o kernel original é o Gram dos dois setores limites. Trata-se de um teorema **condicional sobre esses limites**, não da afirmação de que os checkpoints finitos já os satisfazem.

Assim há uma rota por respostas de uma fonte específica. Uma cota de cauda em norma de operador para todas as entradas continua sendo suficiente e útil, mas não aparece como premissa necessária nesse critério. Também não basta convergir só `X_N`: o setor de energia `B_NX_N` é uma obrigação separada, como num controle de domínio por norma de grafo.

A representação do kernel em todos os pares admissíveis e os controles de coeficientes ainda precisam ser conectados às APIs existentes de diferenças finitas/limites de jets. O presente critério não afirma independência dos jets.

## 5. O que a isometria Cauchy–Laguerre já permite

As provas `cauchyLaguerre_graph_residual_norm` e `cauchyLaguerre_parity_resolvent_gram` mostram que o dicionário literal preserva:

- a norma de `x-z²jx-v`, mapeando separadamente `x`, `jx` e `v`;
- o Gram dos dois setores, incluindo o peso complexo `conj z*w`.

Não é preciso definir um operador em todo o alvo `ℓ²` para conservar esse resíduo de grafo. Ao mesmo tempo, esses teoremas não constroem o `J` físico nem seu fator `B`, não provam que o range seja um carrier espectral redutor e não identificam o passo Hardy com o operador das alturas.

## 6. Replay independente em nove pares finitos

O programa `scripts/study_height_resolvent_green_defect.py` leu somente a diagonal, a subdiagonal, a escala e `moments[0]` do checkpoint nativo de ordem 1536. Os coeficientes de `Φ` foram lidos do cálculo independente por produto de compleção arquivado na auditoria de momentos. Não foram reconstruídos integrando `q_N`.

Para `N→M = 8→16,16→32,32→64`, foram usados três pares de alturas complexas distintas. A resposta de ordem N foi incluída em dimensão M, mantendo a ligação original da borda. Seu resíduo é

$$r_N(z)=-z^2 b_N^{\rm físico}(X_N(z))_N e_{N+1}.$$

A outra resposta usa a matriz completa de ordem M. Esse cruzamento de ordens exercita um resíduo vetorial não nulo, em vez de testar apenas respostas exatas do mesmo truncamento.

No par `z=14+0.02i`, `w=14.2+0.03i`:

| N→M | Norma de r_N(z) | Módulo de δ_N(z) para o polinômio Φ arquivado | Defeito total do kernel cruzado |
|---|---:|---:|---:|
| 8→16 | `8.66232e-7` | `9.75094e-15` | `2.03272e-10` |
| 16→32 | `1.73593e-18` | `3.61133e-38` | `9.03431e-34` |
| 32→64 | `6.85880e-48` | `5.49577e-97` | `2.00482e-92` |

As identidades de energia, borda e decomposição dos defeitos passaram a 180 dígitos, com resíduo relativo máximo de aproximadamente `1.74e-178`, usando `max(1,|lhs|,|rhs|)` no denominador. As cotas foram conferidas numericamente. Todas as componentes dos estados, imagens por J e B, resíduos e valores complexos estão em `audit/height-resolvent-green-study/states.json.gz`.

**Escopo numérico:** a característica usada neste replay é o polinômio independente arquivado de grau 256 em `u=z²`, com derivada calculada diretamente. Isso não é uma certificação da função nativa exata. A comparação entre os graus 128 e 256 ficou abaixo da resolução de trabalho nos pontos escolhidos; isso não certifica a cauda da série, o erro EM ou dígitos nativos. Nenhuma constante, amplitude ou condição de borda foi ajustada.

## 7. Consequência para o programa de alturas

A rota formal atual por resolvente positivo e extração atômica já transforma um zero nativo em autovalor da altura reduzida sob `CompletedNativeRealHPCarrierCertificate`. Ela não precisa do antigo gate adicional `HasGlobalGraphResolventAt`.

O estudo presente atua antes desse certificado. Ele oferece uma identidade e um critério de limite para investigar a realização do kernel original a partir de respostas concretas. A prioridade seguinte é construir essas respostas no carrier da fonte completada, com os canais nativo/compleção e seus cruzamentos preservados, e provar os limites de `r`, `δ` e do setor de energia. O replay de matrizes Jacobi reconstruídas dos momentos não fornece por si essa proveniência física.

## Reprodução

No host `llm`, os comandos focados são:

```bash
lake build --wfail CarrySelfAdjointOperator.NativeCauchyLaguerreResolventDefectAudit
lake env lean -E warning CarrySelfAdjointOperator/NativeCauchyLaguerreResolventDefectAudit.lean
PYTHONDONTWRITEBYTECODE=1 /home/thlinux/miniforge3/bin/python3 \
  scripts/study_height_resolvent_green_defect.py \
  --momentos /home/thlinux/momentos --out .lake/height-resolvent-green-replay
```

O programa usa o ambiente numérico da campanha existente; não acrescenta dependências ao Lake. O resumo arquivado registra os hashes do programa e das duas entradas. A avaliação completa das campanhas 1280/1536 anteriores não foi repetida.

## Verificação formal

O módulo tem 21 declarações públicas: sete definições e 14 teoremas. O build focado com `--wfail` e a execução direta do audit com `-E warning` passaram. O guard percorreu 5.492 constantes nos tipos e corpos e aceitou apenas `propext`, `Classical.choice`, `Quot.sound`. As identidades são condicionadas à igualdade de energia explícita; o teorema de limite também exige os limites listados. Nenhuma hipótese de Gram canônico foi acrescentada para substituir uma prova.

O registro Cauchy–Laguerre passou a cobrir 125 declarações em oito módulos. Também passaram o audit estático, o build raiz com `--wfail` e o build de integração `CarrySelfAdjointOperator.Audit`. Os logs e os metadados da validação estão em `audit/height-resolvent-green-study/`.

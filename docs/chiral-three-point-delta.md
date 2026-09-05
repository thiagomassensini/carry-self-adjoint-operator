# Três pontos radiais e o segundo determinante Hankel nativo

Data: 2026-09-05. Base: `97da9f43a37b56627e0e46b26e76f00bf6e13689`.
Branch: `agent/chiral-three-point-delta`.

## Resultado e fronteira

O Lean identifica o determinante nativo de ordem dois com a expressão proposta nos momentos cosseno. Também prova, com controle do resto ao longo dos passos canônicos, o limite do determinante de três pontos:

$$
\Delta_2=\det G_2=h_0h_2-h_1^2,
\qquad
\lim_{k\to\infty}\frac{\det K(i\varepsilon_k,2i\varepsilon_k,3i\varepsilon_k)}{\varepsilon_k^6}
=4h_1\Delta_2,\qquad \varepsilon_k=\frac1{k+1}.
$$

**A prova Lean de $\Delta_2>0$ permanece aberta.** O laboratório externo com aritmética de bolas Arb, incluindo limites para as duas caudas omitidas, verifica $1.9\cdot10^{-9}<\Delta_2<2\cdot10^{-9}$. Esse cálculo não foi importado como premissa no Lean. A redução formal oferece cinco estimativas integrais suficientes para fechar o sinal.

Não há identificação nova Gamma/Gram nativo em todas as ordens, certificado HP novo, nem merge em `main`. As identidades não usam uma hipótese matemática adicional. Os teoremas condicionais exibem suas estimativas ou a positividade de $\Delta_2$ como argumentos ainda não preenchidos.

## Origem, mapas e destinos usados

1. A representação cosseno existente da característica completada fornece a derivada de ordem seis e o coeficiente $c_3=-\mu_6/720$.
2. A recorrência nativa existente fornece $h_2$ a partir de $c_0,c_1,c_2,c_3$. A matriz usada é a definição existente `hankelGram canonicalCompletedNativeLogDerivativeMoment 2`.
3. Duas integrações por partes transportam os momentos cosseno para os momentos theta já definidos, preservando o termo de cauda com sinal negativo.
4. A matriz de amostras radiais existente é transformada por diferenças finitas. O teorema existente de convergência das diferenças controla o resto; continuidade do determinante conclui o limite de três pontos.

Não se identifica a altura com parâmetro de resolvente. Não se redefine característica, momento, operador, Jacobi, Gamma ou medida espectral.

## Arquivos e declarações

| Arquivo em `CarrySelfAdjointOperator/` | Conteúdo novo |
| --- | --- |
| `CompletedNativeXiCosineMoments.lean` | `iteratedDeriv_six_completedNativeOperatorCharacteristic_zero`; `completedNativeRealEvenCharacteristicCoefficient_three_eq_xiCosineMoment`. |
| `CompletedNativeXiThetaMoments.lean` | `integral_pow_add_two_mul_thetaTailSecond`; `completedNativeXiCosineMoment_succ_eq_thetaTailMoments`; `completedNativeXiCosineMoment_three_eq_thetaTailMoments`. |
| `CompletedNativeSixthOrderHankelGate.lean` | Fórmula exata de $\Delta_2$, equivalências de sinal, complemento de Schur, cinco cotas suficientes e dois witnesses abstratos de insuficiência das cotas antigas. |
| `CompletedNativeRadialThreePointDeterminant.lean` | Congruência por diferenças, escala exata $4\varepsilon^6$, limite do determinante nativo e sinal eventual do determinante condicionado a $\Delta_2>0$. |

Os dois módulos novos entram no aggregator `CarrySelfAdjointOperator.lean`, em `Audit.lean` e em `KernelConstructionAudit.lean`. A lista exata dos 26 teoremas públicos adicionados está em `research/chiral-three-point-delta-2026-09-05/new-theorems.txt`.

Teorema principal sem premissa nova:

```lean
canonicalCompletedNativeRadialThreePointDeterminant_div_sixthStep_tendsto
```

Cadeia central reutilizada, sem reconstruir o final:

```text
canonicalCompletedNativeLogDerivativeMoment_real_recurrence
  + canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio
  + canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant
  + coeficientes cosseno da característica completada
    -> canonicalCompletedNativeHankel_two_det_eq_xiCosineMoments

completedNativePolarizedDslope_shiftedRadial_tendsto
    -> canonicalCompletedNativeRadialThreePointDifferenceMatrix_tendsto
    -> canonicalCompletedNativeRadialThreePointDifferenceMatrix_det_tendsto
  + canonicalCompletedNativeRadialThreePointDifferenceMatrix_det_eq
    -> canonicalCompletedNativeRadialThreePointDeterminant_div_sixthStep_tendsto
```

`canonicalCompletedNativeLowOrderHerglotzCurvaturePositive` e sua equivalência com os momentos fornecem os sinais já provados de $h_0,h_1$. O nome histórico desse teorema não introduz hipótese de Herglotz nesta rodada.

## Fórmula exata e mecanismo de integração por partes

Na notação matemática $\mu_{2j}=\texttt{completedNativeXiCosineMoment}\ j$:

$$
\Delta_2=
\frac{15\mu_2^2\mu_4+3\mu_0\mu_2\mu_6-10\mu_0\mu_4^2}{1440\mu_0^3}.
$$

Declaração: `canonicalCompletedNativeHankel_two_det_eq_xiCosineMoments`. O denominador é estritamente positivo por `completedNativeXiCosineMoment_pos 0`.

Com $A_p=\texttt{completedNativeThetaTailMoment}\ p$, a integração por partes agora está disponível em toda ordem:

$$
\mu_{2n+2}=(2n+2)(2n+1)A_{2n}-\frac14 A_{2n+2}.
$$

Em particular, $\mu_6=30A_4-A_6/4$. Esse mecanismo transporta a próxima estimativa de momento; ele não fornece automaticamente o sinal dos complementos de Schur nas ordens seguintes.

## Por que o fator quatro e a ordem seis são exatos

Para $h=i\varepsilon$, a matriz das diferenças de ordens $0,1,2$ é $T(h)^*S(h)T(h)$, com

$$
T(h)=\begin{pmatrix}
1&-h^{-1}&(2h^2)^{-1}\\
0&h^{-1}&-h^{-2}\\
0&0&(2h^2)^{-1}
\end{pmatrix},\qquad \det T(h)=\frac1{2h^3}.
$$

Portanto, seu determinante é exatamente $\det S(h)/(4\varepsilon^6)$. O limite da matriz de diferenças é

$$
\begin{pmatrix}h_0&0&h_1\\0&h_1&0\\h_1&0&h_2\end{pmatrix},
$$

cujo determinante é $h_1\Delta_2$. A prova formal é um limite ao longo de $\varepsilon_k=1/(k+1)$, usando o teorema existente de diferenças radiais. Não é uma nova prova de uma expansão Taylor em um parâmetro real arbitrário.

## Obrigação analítica residual

A equivalência exata é `canonicalCompletedNativeHankel_two_det_pos_iff_xiSixthMoment`. O primeiro goal Lean é:

```lean
⊢ 10 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 ^ 2 <
    15 * completedNativeXiCosineMoment 1 ^ 2 * completedNativeXiCosineMoment 2 +
      3 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 1 * completedNativeXiCosineMoment 3
```

O goal escalar e os cinco goals suficientes estão copiados da saída do Lean em `research/chiral-three-point-delta-2026-09-05/residual-goals.txt`. A sonda temporária que expõe esses goals é intencionalmente incompleta e fica fora dos módulos e do audit.

Uma rota suficiente, já demonstrada formalmente, é provar:

$$
\mu_0\ge\frac{497}{1000},\quad
\mu_2\ge\frac{287}{12500},\quad
\frac{37}{12500}\le\mu_4\le\frac{593}{200000},\quad
\mu_6\ge\frac{299}{500000}.
$$

A sexta cota, $\mu_0<249/500$, já foi deduzida no Lean da estimativa theta existente `completedNativeThetaTailMoment_zero_gt`. Com essas cotas o numerador é pelo menos

$$\frac{4861191}{50000000000000}>0.$$

Teoremas: `xiSixthMoment_numerator_lower_bound_of_box`, `completedNativeXiCosineMoment_zero_lt_249_div_500`, `canonicalCompletedNativeHankel_two_det_pos_of_xiMoment_bounds`.

Os witnesses `xiFourthMoment_sign_does_not_imply_sixthNumerator` e `thetaTail_coarse_bounds_do_not_imply_sixthNumerator` mostram que os conjuntos de desigualdades antigas enumerados em seus enunciados não implicam o novo sinal para tuplas arbitrárias. **Não são contraexemplos ao kernel nativo**, nem excluem usar a forma específica da densidade theta para provar o sinal.

## Verificação externa e suas caudas

Após $x=e^{2u}$, os mesmos momentos theta são

$$
A_p=\int_1^\infty \left(\frac{\log x}{2}\right)^p x^{-3/4}
\sum_{n=1}^\infty e^{-\pi n^2x}\,dx.
$$

O script `three_point_theta_arb.py` integra os modos $1\le n\le N$ em $1\le x\le B$ com `python-flint==0.9.0` (Arb/Acb). O integrando encaminha o indicador de analiticidade para `log`, conforme a API oficial de `acb.integral`: <https://python-flint.readthedocs.io/en/latest/acb.html#flint.acb.integral>.

Defina a integral exponencial elementar positiva

$$
E_p(a,B)=e^{-aB}\sum_{j=0}^{p}\frac{p!}{(p-j)!}\frac{B^{p-j}}{a^{j+1}}
=\int_B^\infty x^pe^{-ax}\,dx.
$$

Para $x\ge1$, $x^{-3/4}\le1$ e $(\log x/2)^p\le(x/2)^p$. As desigualdades
$n^2\ge1+3(n-1)$ e $(N+1+j)^2\ge(N+1)^2+(2N+3)j$ dão os envelopes:

$$
R_{\rm espacial}\le \frac{E_p(\pi,B)}{2^p(1-e^{-3\pi B})},\qquad
R_{\rm modos}\le \frac{E_p(\pi(N+1)^2,1)}{2^p(1-e^{-\pi(2N+3)})}.
$$

O segundo envelope cobre os modos omitidos em toda a semirreta. Somá-lo ao primeiro pode contar uma região duas vezes, o que preserva a validade da cota superior. O script acrescenta uma bola de raio ao menos igual à soma dos envelopes à integral finita. As fórmulas dos envelopes têm a justificativa acima, mas **essa análise de caudas e o cálculo Arb ainda não foram formalizados no Lean**.

| Execução | Parâmetros | Intervalo externo de $\Delta_2$ |
| --- | --- | --- |
| `arb-128.json` | 128 bits, $N=3$, $B=16$ | $[1.94933555482\cdot10^{-9}\;\pm\;2.77\cdot10^{-21}]$ |
| `arb-192.json` | 192 bits, $N=4$, $B=24$ | $[1.949335554819142214740\cdot10^{-9}\;\pm\;2.86\cdot10^{-31}]$ |

Ambas verificam todas as cotas racionais acima. O certificado externo tem como base de confiança a integração por bolas do Arb e a derivação matemática dos envelopes; ele não pertence ao conjunto de teoremas verificados pelo kernel Lean.

`three_point_theta_lab.py` mantém o diagnóstico independente por quadratura mpmath a 45/65 dígitos e o cálculo polinomial racional exato em SymPy. Os arquivos `quadrature-dps45.json` e `quadrature-dps65.json` registram a convergência de $\det S/\varepsilon^6$ para aproximadamente $2.89847477807\cdot10^{-13}$. Esses dois arquivos não são certificados de intervalos.

Reprodução do certificado externo, a partir da raiz do repositório:

```bash
python3 -m venv /tmp/carry-three-point-interval-venv
/tmp/carry-three-point-interval-venv/bin/pip install python-flint==0.9.0
/tmp/carry-three-point-interval-venv/bin/python research/chiral-three-point-delta-2026-09-05/three_point_theta_arb.py
/tmp/carry-three-point-interval-venv/bin/python research/chiral-three-point-delta-2026-09-05/three_point_theta_arb.py --bits 192 --modes 4 --cutoff 24
```

## Validação e próximo passo

Resultado: build focado com `--wfail` aprovado; audit completo aprovado nos 15 estágios; `git diff --check` aprovado. As 26 verificações `#print axioms` usam apenas `propext`, `Classical.choice` e `Quot.sound`, sem `sorryAx`. Pins e toolchain permanecem idênticos à base.

Os resultados do build, dos 15 estágios atuais de `scripts/audit.sh`, de `#print axioms` e da integridade dos pins constam de `research/chiral-three-point-delta-2026-09-05/validation.txt`. Os logs guardados têm apenas os espaços no fim das linhas removidos para passar em `git diff --check`.

O próximo trabalho matemático está localizado: transformar os envelopes integrais e as estimativas racionais em provas Lean dos cinco goals, ou provar diretamente a desigualdade equivalente do numerador usando a densidade theta. Fechado esse sinal, a cadeia de três pontos já tipada poderá usá-lo. Esta rodada não estabelece positividade em toda ordem nem a identificação Gamma/native Gram.

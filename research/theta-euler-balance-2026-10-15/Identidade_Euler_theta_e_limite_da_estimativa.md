# Identidade Euler da fonte theta e o limite da estimativa curta

Data: 2026-10-15. Fonte canônica: `carry-self-adjoint-operator`, servidor `llm`. Base: `f216103f2c67fa2bd4593943883ded47be4d0410`.

## O que foi obtido

Encontramos e formalizamos uma identidade válida em ordem arbitrária para a mesma família theta. No setor ímpar ela extrai um quadrado escalar não negativo da própria fonte e conserva uma densidade assinada derivada. A hipótese sobre o prefixo anterior é somente **invertibilidade**, sem exigir seu sinal nem o sinal do novo pivô.

Também foi demonstrada uma estimativa inferior em qualquer ordem. A tentativa de torná-la positiva descartando a contribuição positiva da densidade derivada é falsa já na primeira ordem da fonte efetiva. Essa falha foi certificada externamente por aritmética de intervalos Arb, com repetição em outra precisão e número de modos.

A positividade em todas as ordens e a realização pelo transporte físico continuam abertas.

## Objetos preservados

Usamos os objetos existentes, sem mudar a característica completada, o estado sintetizado, a métrica ou amplitudes:

\[
m_k=\texttt{canonicalCompletedNativeLogDerivativeMoment}\ k,
\qquad c_0=\texttt{completedNativeRealEvenCharacteristicCoefficient}\ 0>0,
\]

\[
\mathcal I(P)=\int_0^\infty P(u)\Phi(u)\,du,
\qquad \mathcal I(P_k)=m_k.
\]

Aqui \(\Phi\) é o kernel Xi–theta positivo original e \(P_k\) são os polinômios `nativeThetaMomentPolynomial`, gerados pela fonte antes de qualquer afirmação de positividade Hankel.

Para o prefixo Hankel \(H_{s,n}=(m_{i+j+s})\), o acoplamento \(b_{s,n}=(m_{i+n+s})\) e a direção crítica existente

\[
v=(-H_{s,n}^{-1}b_{s,n},1),
\]

definimos apenas notação para os objetos já construídos:

\[
Q_{s,n}(u)=c_0\sum_{i,j=0}^{n}v_iv_jP_{i+j+s}(u),
\qquad R_{s,n}=\mathcal I(Q_{s,n}).
\]

A inversa escolhe a direção de eliminação do Schur existente; ela não define uma nova fonte física. A leitura escalar é aplicada ao estado completado já sintetizado.

## Uma recorrência diferencial em todas as ordens

Se \(\mathscr E P(u)=uP'(u)\), o novo teorema `nativeThetaEulerPolynomial_eq` prova

\[
\boxed{
\mathscr E P_k=(2k+2)P_k
-2\sum_{a=0}^{k-1}m_aP_{k-1-a}.
}
\]

A prova usa a válvula projetiva existente. Escrevendo \(C(t)\) para a série da característica e \(V=C(0)/C\), já temos \(V'=mV\). A série dos polinômios é

\[
\mathcal P(u,t)=V(t)\,c_0^{-1}\mathcal N(u,t),
\quad
\mathcal N(u,t)=\sum_{k\ge0}\frac{(-1)^k(k+1)u^{2k+2}}{(2k+2)!}t^k.
\]

O numerador satisfaz \(u\partial_u\mathcal N=2(\mathcal N+t\partial_t\mathcal N)\). A regra do produto e a equação da válvula dão a recorrência acima por extração de coeficientes. Tudo acontece nas mesmas séries formais; não se introduz hipótese de convergência ou de positividade do kernel desejado.

## Por que aparece um quadrado

Considere a convolução

\[
C_k=\sum_{a<k}m_am_{k-1-a},\qquad C_0=0.
\]

A invertibilidade do prefixo anterior fornece exatamente a ortogonalidade

\[
\sum_{j=0}^n v_jm_{a+j+s}=0\quad(a<n).
\]

Os novos teoremas de cancelamento, válidos para qualquer sequência real com essa ortogonalidade, provam

\[
\sum_{i,j=0}^n v_iv_jC_{i+j}=0\quad(s=0),
\]

\[
\boxed{
\sum_{i,j=0}^n v_iv_jC_{i+j+1}
=\left(\sum_{i=0}^nv_im_i\right)^2\quad(s=1).
}
\]

A prova divide a convolução em duas pernas completas. Cada perna cancela pela ortogonalidade ao prefixo anterior. No setor ímpar sobra o produto central \(m_im_j\), cujo somatório é o quadrado exibido. Todos os pares \((i,j)\) são conservados até essa identidade; não se apagaram termos cruzados.

## A identidade uniforme da fonte

Defina

\[
D_{s,n}(u)=uQ'_{s,n}(u),\qquad
\eta_n=\sum_{i=0}^nv_im_i\quad\text{na direção crítica do setor ímpar}.
\]

Os teoremas `nativeSchurEuler_odd_balance` e `nativeSchurEuler_even_balance` dão, para qualquer \(n\) com o prefixo correspondente invertível,

\[
\boxed{
(4n+4)R_{1,n}=2c_0\eta_n^2+\mathcal I(D_{1,n}),
}
\]

\[
\boxed{(4n+2)R_{0,n}=\mathcal I(D_{0,n}).}
\]

O quadrado ímpar é não negativo. É um quadrado de uma leitura escalar fixa dos momentos; ainda não é uma igualdade com a energia do transporte físico. O setor par não recebe esse termo adicional.

A derivada atua no polinômio finito, mantendo o peso \(\Phi\). A formalização usa sua integrabilidade já estabelecida, sem descartar termos de fronteira por uma integração por partes adicional.

## Estimativa inferior e a obrigação que permanece

Separe as massas de \(D_{1,n}\) usando o mesmo peso positivo original. A igualdade formalizada é

\[
(4n+4)R_{1,n}=2c_0\eta_n^2+M^+(D_{1,n})-M^-(D_{1,n}).
\]

Consequentemente,

\[
\boxed{
R_{1,n}\ge\frac{2c_0\eta_n^2-M^-(D_{1,n})}{4n+4}.
}
\]

Essa estimativa é válida em ordem arbitrária, mas seu lado direito pode ser negativo. O critério exato de sinal é

\[
R_{1,n}>0\iff M^-(D_{1,n})<2c_0\eta_n^2+M^+(D_{1,n}).
\]

A identidade separa um termo não negativo e explicita o restante. Ela não demonstra a desigualdade geral do lado direito, que continua sendo uma obrigação substancial da fonte.

## A estimativa curta falha na fonte efetiva

Uma tentativa natural seria exigir apenas \(M^-(D_{1,n})<2c_0\eta_n^2\). O novo módulo `NativeSchurEulerFirstOdd.lean` calibra a primeira ordem:

\[
Q_{1,0}(u)=\frac{m_0}{2}u^2-\frac{u^4}{12},
\quad D_{1,0}(u)=m_0u^2-\frac{u^4}{3},
\quad \eta_0=m_0,
\]

\[
\mathcal I(D_{1,0})=4c_0m_1-2c_0m_0^2.
\]

O script `scripts/certify_theta_euler_first_odd_bound.py` integra a parte positiva de \(D_{1,0}\Phi\) até sua raiz \(\sqrt{3m_0}\), com erro dos modos omitidos e da extremidade incerta incluídos. A massa negativa segue da identidade assinada exata.

A certificação Arb em 384 bits/8 modos e a repetição em 512 bits/10 modos fornecem intervalos sobrepostos e estritos:

\[
\frac{M^-(D_{1,0})}{2c_0m_0^2}
\approx1.004824787249784>1,
\]

\[
M^-(D_{1,0})-2c_0m_0^2
\approx2.56083599786551\times10^{-6}>0.
\]

A contribuição positiva da derivada é aproximadamente \(7.64779219337681\times10^{-5}\) e restaura o balanço completo positivo \(4c_0m_1\). Portanto, eliminar essa parcela torna a estimativa insuficiente já no caso inicial. Isso refuta essa simplificação específica; não refuta a positividade da fonte nem outras estimativas.

**Status:** são certificados externos de intervalos, não provas numéricas incorporadas ao Lean. Nenhum certificado é uma premissa dos teoremas formais.

A entrada dos scripts é o certificado theta publicado de 1024 bits. Seus dados são momentos da **cauda theta**, convertidos nos coeficientes da característica pela fórmula Green já existente:

\[
c_0=\tfrac12-A_0/4,\qquad
c_j=(-1)^j\left(\frac{A_{j-1}}{(2j-2)!}-\frac{A_j}{4(2j)!}\right).
\]

Eles não são lidos como momentos brutos do kernel Xi. O novo cálculo integra massas da densidade derivada; não refaz a integração dos momentos da fonte.

Uma exploração separada com `mpmath` reproduziu o balanço para \(n=0,1,2\) em 80 casas, com erros relativos inferiores a \(10^{-75}\). Nela a razão massa negativa/quadrado cresce aproximadamente de \(1.0048\) para \(4.8122\) e \(44.2207\). Esses dois valores superiores são evidência exploratória, sem certificação de intervalos e sem extrapolação para todas as ordens.

## Próxima obrigação concreta

A investigação encontrou uma identidade uniforme da fonte e um termo não negativo que emerge do cancelamento exato das convoluções. O controle restante precisa manter conjuntamente esse quadrado e a parte positiva da densidade derivada. A tentativa de usar apenas o quadrado já foi rejeitada pela fonte efetiva.

O próximo alvo é uma estimativa para o balanço completo de \(D_{1,n}\), usando sua recorrência diferencial e a estrutura theta, junto com o controle do setor par. Qualquer passo de indução ainda precisa demonstrar essa estimativa e preservar a invertibilidade dos prefixos. A positividade em todas as ordens, o residual infinito e o transporte para um defeito físico permanecem abertos.

## Validação e reprodução

- `lake build --wfail CarrySelfAdjointOperator.NativeSchurEulerBalanceAudit`: sucesso, 9840 jobs.
- `lake build --wfail`: sucesso, 10213 jobs.
- 28 raízes públicas, fechamento de 5842 declarações por tipos e corpos; somente `propext`, `Classical.choice`, `Quot.sound`.
- Nenhum `sorry`, `admit`, novo axioma ou alteração do manifesto. Os arquivos C2 preexistentes foram preservados.

Certificados externos, com Python Miniforge e `python-flint`:

```sh
/home/thlinux/miniforge3/bin/python3 scripts/certify_theta_euler_first_odd_bound.py \
  --bits 384 --modes 8 --output /tmp/theta-euler-bound-384.json
/home/thlinux/miniforge3/bin/python3 scripts/certify_theta_euler_first_odd_bound.py \
  --bits 512 --modes 10 --replication /tmp/theta-euler-bound-384.json \
  --output /tmp/theta-euler-bound-512.json
```

A exploração em `probe_euler_masses.py` usa `mpmath` e pontos médios dos intervalos de entrada; seus resultados não são certificados. Os arquivos `theta-euler-bound-384.json` e `theta-euler-bound-512.json` contêm os intervalos Arb e os hashes de proveniência.

# Teorema da reconstrução causal e da unicidade admissível

## Objetivo

Registrar formalmente a observação estrutural de que a geometria bracketada
não fornece apenas sondas de um estado já conhecido. Cada célula fornece uma
lei causal exata: conhecidos a perna esquerda, o centro e o bracket, a perna
direita é forçada. A repetição dessa lei reconstrói o estado inteiro.

O resultado usa somente a geometria aditiva do bracket e a organização das
câmeras nativas. Não requer estrutura multiplicativa nem qualquer objeto
externo à teoria.

## 1. A identidade local

Seja `A` um grupo comutativo aditivo e seja um estado

\[
x:\mathbb N\longrightarrow A.
\]

Defina o bracket causal unitário, indexado por sua perna esquerda, por

\[
B_x(n)=x_n-2x_{n+1}+x_{n+2}.
\]

Então vale identicamente

\[
\boxed{x_{n+2}=B_x(n)-x_n+2x_{n+1}.}
\]

Portanto, se dois estados possuem a mesma perna esquerda, o mesmo centro e o
mesmo bracket numa célula, eles possuem necessariamente a mesma perna direita.
Essa é a forma precisa de "conhecer o lado esquerdo e o centro determina o lado
direito": o bracket da célula é o dado geométrico que realiza a determinação.

## 2. Teorema global de reconstrução

Fixe os dados

\[
\mathcal D=(a_0,a_1,b),
\qquad a_0,a_1\in A,
\qquad b:\mathbb N\to A.
\]

Defina recursivamente

\[
\begin{aligned}
x^{\mathcal D}_0&=a_0,\\
x^{\mathcal D}_1&=a_1,\\
x^{\mathcal D}_{n+2}
  &=b_n-x^{\mathcal D}_n+2x^{\mathcal D}_{n+1}.
\end{aligned}
\]

### Teorema (existência e unicidade causal)

Para todo dado `D`, existe um único estado `x` tal que

\[
x_0=a_0,\qquad x_1=a_1,
\qquad B_x(n)=b_n\quad\text{para todo }n\in\mathbb N.
\]

Esse estado é exatamente a reconstrução recursiva
\(x=x^{\mathcal D}\).

### Demonstração

Existência: substituindo a recorrência na definição do bracket,

\[
\begin{aligned}
B_{x^{\mathcal D}}(n)
 &=x^{\mathcal D}_n-2x^{\mathcal D}_{n+1}
   +x^{\mathcal D}_{n+2}\\
 &=x^{\mathcal D}_n-2x^{\mathcal D}_{n+1}
   +b_n-x^{\mathcal D}_n+2x^{\mathcal D}_{n+1}\\
 &=b_n.
\end{aligned}
\]

Unicidade: sejam `x` e `y` duas realizações. Elas coincidem em `0` e `1`.
Se coincidem em `n` e `n+1`, a identidade local e a igualdade dos brackets
implicam

\[
x_{n+2}=B_x(n)-x_n+2x_{n+1}
       =B_y(n)-y_n+2y_{n+1}=y_{n+2}.
\]

A indução em dois passos conclui que `x=y` em toda profundidade.

### Forma telescópica de todas as ordens

Defina a inclinação discreta

\[
d_n=x_{n+1}-x_n.
\]

O bracket é exatamente a variação dessa inclinação:

\[
\boxed{B_x(n)=d_{n+1}-d_n.}
\]

Daí seguem duas telescopias exatas:

\[
d_n=d_0+\sum_{j=0}^{n-1}B_x(j)
\]

e

\[
x_n=x_0+\sum_{k=0}^{n-1}d_k.
\]

Combinando-as, obtemos a reconstrução fechada válida em toda ordem:

\[
\boxed{
x_n=x_0+\sum_{k=0}^{n-1}
\left((x_1-x_0)+\sum_{j=0}^{k-1}B_x(j)\right).
}
\]

Para os dados \(\mathcal D=(a_0,a_1,b)\), isso se torna

\[
\boxed{
x^{\mathcal D}_n=a_0+\sum_{k=0}^{n-1}
\left((a_1-a_0)+\sum_{j=0}^{k-1}b_j\right).
}
\]

Essa é a expressão literal de que as pernas telescopam: o primeiro nível
transporta brackets para inclinações e o segundo transporta inclinações para
o estado.

## 3. Corolário de unicidade positiva/admissível

Seja `Adm(x)` qualquer predicado adicional sobre estados. Ele pode representar,
por exemplo, positividade, energia finita, pertencimento ao domínio do operador,
uma condição de bordo, ou a conjunção dessas propriedades.

### Corolário (estado admissível único)

Se a reconstrução canônica \(x^{\mathcal D}\) satisfaz `Adm`, então existe um
único estado que simultaneamente:

1. satisfaz `Adm`;
2. possui sementes `a₀,a₁`;
3. realiza o campo de brackets `b`.

Em símbolos,

\[
\operatorname{Adm}(x^{\mathcal D})
\Longrightarrow
\exists!x\,\bigl(
  \operatorname{Adm}(x)\land
  x_0=a_0\land x_1=a_1\land
  \forall n,\ B_x(n)=b_n
\bigr).
\]

A distinção lógica é importante:

- a geometria causal prova existência e unicidade da realização;
- uma identidade de Green ou uma identidade de energia pode certificar que
  essa realização é positiva/admissível;
- depois dessa certificação, não existe uma segunda realização positiva com
  os mesmos dados.

Assim, positividade não escolhe arbitrariamente um elemento entre várias
soluções. A geometria já eliminou a multiplicidade.

## 4. Presença dessas células no atlas de todas as bases

Para toda profundidade central `c ≥ 3`, a câmera natural de rótulo `c`
possui:

\[
\operatorname{alignedCenter}(c,0)=c
\]

e contém o raio unitário. Portanto, colocando `c=n+1`, a primeira célula de
raio `1` da câmera `n+1` é precisamente

\[
(n,n+1,n+2),
\]

e seu bracket centrado é exatamente `B_x(n)`.

Logo, o atlas multibase natural contém todas as células causais unitárias a
partir de `n ≥ 2`. Em particular:

### Corolário (unicidade no atlas multibase)

Dois estados que coincidem nas quatro coordenadas baixas

\[
x_0=y_0,\quad x_1=y_1,\quad x_2=y_2,\quad x_3=y_3
\]

e possuem brackets iguais na primeira célula unitária de toda câmera natural
`c ≥ 3` coincidem em todas as profundidades.

As quatro sementes aparecem porque o atlas natural cobre causalmente a cauda
a partir de `n=2`. A cauda inteira já é determinada apenas por `x₂`, `x₃` e
essas células; `x₀` e `x₁` completam o setor inferior que não é atravessado
por essa família natural de câmeras.

## 5. Relação estrutural com telescopia e cutoff

A mesma relação aparece em duas escalas:

- localmente, uma célula transporta `esquerda + centro + bracket` para a perna
  direita;
- globalmente, as pernas consecutivas se identificam e a propagação
  telescopa através da profundidade;
- num cutoff geometricamente completo, a última perna direita não fica
  indeterminada: ela é exatamente a extremidade da última célula completa.

Portanto, a recorrência, a telescopia e o fechamento geométrico do cutoff são
três apresentações da mesma relação de compatibilidade.

## 6. Estatuto formal

O arquivo Lean correspondente é
`CausalBracketPositiveStateUniqueness.lean`. Nele foram formalizados:

- a identidade exata da perna direita;
- a reconstrução por indução em dois passos;
- as duas identidades de telescopia e a fórmula fechada de todas as ordens;
- a realização exata de todos os brackets;
- a existência e unicidade global;
- o corolário para qualquer predicado de admissibilidade;
- a presença das células causais no atlas de todas as bases;
- a unicidade da cauda e a unicidade global multibase.

O arquivo foi compilado sem `sorry` e sem dependência de `sorryAx`.

## 7. Forma condensada

\[
\boxed{
\text{bracket local}
\Longrightarrow
\text{perna direita forçada}
\Longrightarrow
\text{propagação causal}
\Longrightarrow
\text{estado global único}
}
\]

e, quando uma identidade de energia certifica admissibilidade,

\[
\boxed{
\text{estado reconstruído admissível}
\Longrightarrow
\text{único estado admissível compatível com a geometria}.
}
\]


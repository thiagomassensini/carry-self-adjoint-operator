# Órbita residual dos centros e pernas

## Objetivo

Registrar a passagem exata da geometria inteira de uma câmera para seu
quociente cíclico. Esta passagem não cria um modelo novo: ela apenas esquece o
número do bloco e preserva o canal residual ocupado pelo centro e pelas duas
pernas.

Para uma câmera suportada, escreva

\[
d=\operatorname{cameraSlope}(b),
\qquad c_i=d(i+1),
\qquad 0<r<d.
\]

Transportamos as três posições para o grupo cíclico

\[
\mathbb Z/d\mathbb Z.
\]

## Forma normal dos canais

O ledger residual exato é

\[
\boxed{
(c_i,c_i-r,c_i+r)
\longmapsto
(0,-r,r)
\quad\text{em }\mathbb Z/d\mathbb Z.
}
\]

Portanto, o número do centro `i` desaparece no quociente, mas os papéis
geométricos não desaparecem:

- o centro ocupa o canal zero;
- a perna direita ocupa o canal `r`;
- a perna esquerda ocupa o canal `-r`.

## Reflexão canônica

Considere a involução

\[
\rho_d(a)=-a.
\]

Ela fixa o centro e troca literalmente as pernas:

\[
\rho_d(0)=0,
\qquad
\rho_d(r)=-r,
\qquad
\rho_d(-r)=r.
\]

Assim, o setor das pernas de raio `r` é a órbita

\[
\mathcal O_r=\{r,-r\}.
\]

Lean prova que essa órbita é exatamente o par não ordenado dos dois canais
literais emitidos pelo bracket, e não apenas um conjunto que os contém.

## Separação do centro

Como `0<r<d`, o canal de raio não é zero. Consequentemente,

\[
\boxed{\{0\}\cap\mathcal O_r=\varnothing.}
\]

Esta é a versão no quociente da não divisibilidade das pernas. Ela diz que
o setor fixo central e o setor de pernas são disjuntos antes da introdução de
qualquer peso, produto interno ou operador espectral.

## Ponto fixo antipodal

Os pontos fixos abstratos de `ρₑ` satisfazem

\[
a=-a.
\]

No grupo cíclico, isso equivale a

\[
a=0
\quad\text{ou}\quad
2a=d
\]

quando `a` é representado no intervalo canônico. Para um raio emitido, o caso
zero já foi excluído. Logo,

\[
\boxed{
\rho_d(r)=r
\Longleftrightarrow
2r=d.
}
\]

Daí segue a contagem exata:

\[
|\mathcal O_r|=
\begin{cases}
1,&2r=d,\\
2,&2r\ne d.
\end{cases}
\]

O canal antipodal não se torna centro. Ele é um ponto fixo não central da
reflexão: as duas incidências inteiras continuam distintas, mas possuem a
mesma classe residual.

## Relação com o próximo operador

Esta etapa fornece uma decomposição combinatória canônica:

\[
\text{setor central }\{0\}
\quad\sqcup\quad
\text{órbitas de pernas }\{r,-r\}.
\]

O próximo passo natural é transportar a reflexão para o espaço de funções
sobre `ZMod d`. Ali ela se torna uma involução linear e produz, sem escolha
arbitrária, os setores simétrico e antissimétrico das pernas. Essa passagem
ainda é finita e geométrica; não identifica por si só o limite analítico ou um
espectro de alturas.

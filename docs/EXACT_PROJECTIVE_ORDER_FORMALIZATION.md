# Identidade projetiva exata e lei de `ORDER`: mapa de formalização

Data de integração: 22 de agosto de 2026.

Este arquivo conecta ao repositório as notas:

- `IDENTIDADE_PROJETIVA_EXATA_LIMITE_OPERADOR_ALTURAS.md`;
- `IDENTIDADE_EXATA_ORDEM_JACOBI_OPERADOR_ALTURAS_GITHUB_VSCODE.md`.

A separação abaixo é deliberada. Uma identidade numericamente auditada não é
marcada como teorema Lean antes de existir uma declaração compilada que diga a
mesma coisa.

## 1. Agora em nível de teorema

### 1.1 Torre Hankel

Já estavam formalizadas as restrições principais exatas

```text
G_N = principal block of G_(N+1)
K_N = principal block of K_(N+1)
```

por `hankelGram_succ_principal` e `shiftedHankel_succ_principal`.

### 1.2 Álgebra de bloco da congruência Jacobi

Já estava formalizada a implicação

```text
lower block extension of whitening
+ principal block extension of shifted Hankel
=> principal block identity of the Jacobi congruence
```

em `ProjectiveJacobiTower.lean`.

### 1.3 Limite cilíndrico exato de uma torre projetiva

`ExactProjectiveMatrixTower.lean` acrescenta:

```text
IsExactPrincipalTower
IsExactPrincipalTower.submatrix_of_le
exactPrincipalTowerLimit
exactPrincipalTowerLimit_submatrix
ExactProjectiveJacobiTower.limitMatrix_submatrix
```

Assim, se a lei principal consecutiva é conhecida, todas as ordens são
compatíveis e a família determina uma única matriz infinita entrada por
entrada. Cada seção finita é recuperada exatamente. Isso constrói o objeto
algébrico cilíndrico, não ainda um operador fechado em um Hilbert completado.

### 1.4 Recorrência abstrata de Jacobi e defeito do nível seguinte

`JacobiOrderPolynomial.lean` define a sequência pela recorrência

\[
P_{n+2}(y)
=(y-\alpha_{n+1})P_{n+1}(y)-\beta_n^2P_n(y)
\]

e prova que, se `P_(n+1)(y)=0`, então

\[
P_{n+2}(y)=-\beta_n^2P_n(y).
\]

Também fica formalizada a identidade telescópica finita de qualquer cauda de
ordem:

\[
\sum_{r<k}(t_{N+r}-t_{N+r+1})=t_N-t_{N+k}.
\]

## 2. Gate canônico da torre projetiva

O repositório já constrói em cada ordem o whitening canônico por LDL:

```text
canonicalLDLInverseFactor
canonicalLDLInverseFactor_whitens
canonicalHankelWhitening
```

Ainda falta provar que esses fatores são compatíveis entre ordens. O alvo
concreto é uma declaração que implique:

```text
IsExactJacobiWhiteningTower moments
  (fun N => canonicalHankelWhitening moments N (hgram N))
```

A rota matemática das notas é a unicidade do fator triangular inferior com
diagonal positiva. Uma prova alternativa pode usar diretamente a
compatibilidade por prefixo do Gram--Schmidt que define `LDL.lowerInv` no
Mathlib.

Sem esse teorema, o limite matricial já está formalizado para qualquer torre
compatível, mas ainda não foi instanciado automaticamente pela família LDL
canônica.

## 3. Gate de tridiagonalidade

A sequência `jacobiOrderPolynomial` está formalizada pela recorrência. Falta
provar que a matriz concreta

```text
canonicalFiniteJacobiSection moments N hgram
```

é tridiagonal e que seu polinômio característico coincide com essa sequência.
Esse teorema deve vir da multiplicação por `y` na base ortonormal produzida
pelos momentos, isto é, da recorrência de três termos dos polinômios
ortogonais.

Somente depois dessa identificação serão legítimos, para a matriz concreta:

- `jacobiCharPolySucc`;
- defeito do autovalor antigo no nível novo;
- interlacing estrito do ramo extremo;
- fórmula exata do incremento do maior autovalor;
- fórmula exata do incremento da altura.

## 4. Gate Green--TFVD--Hankel

A BR2 já formaliza a cadeia estrutural:

```text
center--leg diagonal impossible
=> bracket incidences linearly independent
=> off-diagonal Green coefficient certificate gives the full Gram kernel
=> both Hankels positive semidefinite
=> injective incidence-to-jet transport gives positive definiteness
=> finite height operator is symmetric
```

Ainda é necessário construir, para o estado completado concreto:

1. `BR2CenterLegGreenMomentCertificate`;
2. `BR2BracketIncidenceJetTransport`;
3. as realizações Green division-free dos canais de completion e native/C3.

A identidade Wronskiana das notas especifica o `momentReadout` correto:

\[
\frac{q(u)-\overline{q(v)}}{u-\bar v}
=\sum_{i,j\ge0}h_{i+j+1}u^i\bar v^j.
\]

O TFVD enriquecido deve fornecer o `greenOffDiagonalReadout` sem apagar
valor, log-jet, proveniência, setor off-diagonal ou completion.

## 5. Camada infinita ainda não reivindicada

A matriz infinita entrada por entrada não é, sozinha, uma realização
autoadjunta. Permanecem separados:

- definição do operador mínimo em `c00`;
- positividade e limitabilidade da forma;
- closability e fechamento;
- unicidade da extensão autoadjunta;
- exclusão de massa em `0`, equivalente a `ker J = {0}`;
- domínio de `J^(-1/2)`;
- convergência forte de resolventes;
- cauda infinita em `ORDER`;
- bounds quantitativos para a visibilidade do bordo.

## 6. Ordem de ataque

```text
Green/TFVD concrete coefficient certificate
-> strict Hankel positivity in every order
-> compatibility of canonical LDL whitening
-> exact canonical Jacobi tower
-> concrete tridiagonality
-> characteristic-polynomial recurrence
-> interlacing and exact ORDER increment
-> minimal infinite Jacobi operator
-> functional calculus T = J^(-1/2)
```

Essa ordem mantém separados o fechamento algébrico da torre, a análise do
estado completado e a realização operatorial infinita.

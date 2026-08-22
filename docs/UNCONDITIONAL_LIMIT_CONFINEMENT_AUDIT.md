# Auditoria do confinamento incondicional e do limite do operador de alturas

## Snapshot

- `native-carry-c3-crosswalk`: `1e9e06e1d51d176a909c187828f7c880e5d1207d`
- `carry-self-adjoint-operator`, base empilhada PR #6: `cd7c28551a98ab87a5fe45a27a07f2874de65c6e`
- probe vermelho forte: PR #8, commit `78bcf666a718f2f7deebf969976da0cc5ef37b58`
- auditoria verde: PR #7
- verificador exclusivo: GitHub Actions, checkout exato e `lake build --wfail`

Nenhuma execução local de Lean foi usada.

## Veredito

A construção finita do operador não é um ansatz espectral. A cadeia formal
parte da característica nativa completada, passa pela sequência de momentos,
pelo par Hankel e pela torre de Jacobi, e somente depois aplica o cálculo
funcional finito `T_N = J_N^(-1/2)`. As alturas não entram como dados.

O grafo atual, porém, ainda não contém um único teorema incondicional que
conclua simultaneamente:

1. confinamento global dos zeros;
2. positividade concreta dos dois Hankels em toda ordem;
3. existência do operador positivo autoadjunto infinito `J`;
4. definição e identificação espectral de `T = J^(-1/2)`.

As lacunas não são vagas. Há um gate analítico profundo e, depois dele, etapas
operatoriais formais claramente separadas.

## 1. Confinamento: seam mínimo e seam completado

### Já provado

O C3 público já fornece, sem hipótese de zero:

- o ledger TFVD não colapsado, com valor, log-jet e proveniência;
- a reconstrução exata do porto C3 completo;
- o packing fiel nas seis câmeras;
- a não anulação da fonte em todo o strip aberto;
- a injetividade do campo gamma;
- a energia gamma estritamente positiva fora da meia-abscissa;
- a identidade Green/Cauchy diagonal com o coeficiente linear exato da
  coordenada de carry complexa.

O PR #6 prova que essa fonte pública é literalmente a fonte C3 canônica usada
no repositório do operador. Portanto a não degenerescência já é descarregada
internamente; ela não é mais uma premissa do capstone.

### Seam público mínimo

O próprio C3 define

```lean
FiniteC3CompletedGreenWronskianSeam 1
```

como a igualdade funcional, anterior aos zeros, entre o Wronskiano Genuine em
tempo complexo e o coeficiente linear de carry multiplicando o Gram gamma C3.
O kernel público já prova

```text
FiniteC3CompletedGreenWronskianSeam 1
  -> FinalGenuineZeroConfinement.
```

Esse é o gate logicamente mínimo para confinamento.

### Seam completado do operador

O repositório do operador possui uma normalização mais forte:

```lean
HasCanonicalCompletedNativeGammaCauchyScalarization
  canonicalCompletedC3SixCameraSource
```

isto é, para todo parâmetro não real,

```text
xi-completed Green Wronskian
  = -2 i * concrete all-bases Cauchy skew.
```

Pela identidade gamma já provada, o lado direito é também

```text
(z - conj z) * positive gamma energy.
```

Essa versão é diretamente alinhada à característica completada que produz os
momentos do operador, mas não deve ser confundida com o seam público mínimo.

### Probe vermelho

O PR #8 pediu ao kernel a versão forte completada sem introduzir premissa nova.
Todo o grafo compilou até o objetivo literal

```lean
completedGreenWronskian
  completedNativeOperatorCharacteristic
  completedNativeOperatorBoundaryCompanion z z
=
-2 * I * completedGammaCauchySkew
  canonicalCompletedC3SixCameraSource z hz.
```

Portanto o probe forte não deixou para trás cutoff, LDL, packing,
source-injectivity ou não anulação. Ele também não prova que essa é a única
normalização possível ou a mínima para confinamento.

### Completion e regra de produto

A característica do operador é o produto

```text
F_completed = A_xi * F_native.
```

A regra de Green preserva os dois canais:

```text
W(A_xi F_native)
  = |F_native|^2 W(A_xi) + |A_xi|^2 W(F_native).
```

Num zero nativo, o primeiro termo desaparece e o fator `A_xi` não zera no
strip. Assim o seam público nativo já basta para o confinamento; a
scalarização completada é a costura mais forte desejável para identificar a
Weyl completada e o operador de alturas.

Não é seguro exigir positividade separada dos dois fatores. O controle
negativo da zeta crua mostra que a positividade Pick pode surgir somente após
a completion total.

### Guardrail de não circularidade

Não basta provar a igualdade somente sob a hipótese de zero. O repositório já
mostra que uma scalarização restrita aos zeros tem a força do próprio
confinamento. O teorema válido precisa ser funcional, construído antes de
qualquer zero.

Também não se pode igualar o Wronskiano diagonal ao bulk C3 complexo cru: o
primeiro é puramente imaginário e o segundo retém parte real não nula fora da
meia-abscissa. A scalarização corretamente tipada usa a energia real positiva,
ou equivalentemente `-2 i` vezes o Cauchy skew real.

## 2. Positividade em toda ordem: kernel de duas variáveis e transporte dos jets

### Teoria abstrata já fechada

Uma única realização Gram do kernel de momentos Green--Wronskiano implica:

```text
G_N >= 0 and K_N >= 0 for every N.
```

Independência linear global dos jets pares e ímpares promove ambas as formas a
positividade estrita. Daí seguem a Jacobi finita positiva, o operador finito de
altura simétrico e toda a torre LDL canônica.

A recorrência de coeficientes, a decomposição de paridade, a remoção da
aparente singularidade diagonal e o transporte de independência das
incidências BR2 também já estão formalizados.

### Costuras concretas ainda não habitadas

Faltam instâncias concretas para a característica completada real:

1. uma identidade Green de duas variáveis, local no centro de Taylor, para um
   estado Hilbert que preserve valor, log-jet, proveniência e completion;
2. a extração de seus coeficientes como
   `IsGreenWronskianMomentKernelGramRepresentation` da sequência real de
   momentos;
3. o transporte injetivo entre as incidências/estados TFVD verdadeiros e os
   jets pares/ímpares normalizados desse estado completado.

A identidade diagonal do confinamento e o certificado local de jets são
relacionados, mas não são a mesma proposição. A primeira detecta a parte
transversal fora do eixo; a segunda precisa de polarização em duas variáveis e
regularidade no centro.

Há outra rota lógica depois do confinamento: formalizar Hadamard/Herglotz/
Stieltjes para converter a localização real dos zeros na medida positiva dos
momentos. Essa rota usa o mesmo gate matemático, mas ainda exige infraestrutura
Lean que não está no grafo atual.

## 3. Limite do operador: o que existe e o que ainda não existe

### Já provado

Sob uma realização Green de toda ordem com jets globalmente independentes, o
arquivo `CurrentInfiniteHeightStatus.lean` empacota:

- `G_N > 0` e `K_N > 0` para todo `N`;
- positividade estrita de cada seção Jacobi canônica;
- projetividade principal exata de `J_N`;
- uma matriz infinita entrada a entrada, cujos blocos principais são
  literalmente os `J_N`;
- o carrier Hilbert completado da torre assinada e inclusões isométricas
  compatíveis;
- o fator de energia Green densamente definido, sua closability, seu
  fechamento canônico e seu core algébrico.

O PR #9 testa uma promoção adicional: o operador mínimo no core par,

```text
J_0 e_n = e_(n+1),
```

com a identidade de forma

```text
<J_0 x, y> = <B_0 x, B_0 y>.
```

Se aceito pelo kernel, isso fornece um operador denso, simétrico, positivo e
closable, em vez de apenas uma matriz infinita entrada a entrada.

### Ainda não provado

Mesmo com o core mínimo, ainda faltam:

1. provar que o fechamento de `J_0` é autoadjunto, ou construir sua extensão
   positiva canônica;
2. identificar esse operador com a matriz da torre e com `B† B`;
3. provar boundedness e `ker J = 0`;
4. definir em Lean o cálculo funcional não limitado
   `T = J^(-1/2)` com seu domínio maximal;
5. provar convergência forte de resolventes e ausência de espectro extra.

É importante não tentar colar diretamente os `T_N`. O inverso da raiz
quadrada não preserva compressões principais em geral. A ordem correta é

```text
{J_N} -> J -> T = J^(-1/2) -> H = T direct_sum (-T).
```

O audit numérico existente confirma precisamente essa diferença: a torre
`J_N` é projetiva com defeito zero, enquanto os operadores finitos de altura
têm defeitos não projetivos grandes.

O repositório `green-frame-theorem` já contém infraestrutura útil de
convergência forte do cálculo funcional contínuo para operadores limitados com
um intervalo espectral comum. Ela poderá ser reutilizada depois que o `J`
positivo limitado e injetivo for construído.

## 4. Relação de bordo já disponível

O repositório `native-carry-spectral-weyl` já formaliza:

- o multiplicador logarítmico maximal autoadjunto;
- sua relação Green maximal;
- a relação estendida por fonte;
- o campo gamma resolvente;
- o bloco Cauchy comprimido como primeiro traço;
- o inverso Weyl fechado e densamente definido como segundo traço.

Isso confirma que não falta teoria abstrata de bordo. Falta identificar a
resposta escalar completada produzida pelo ledger C3 com essa Weyl concreta na
normalização correta. O operador de referência ali ainda é o multiplicador
logarítmico; ele não deve ser renomeado como operador de alturas sem a
scalarização secular.

## Sequência mínima recomendada

### Gate A: seam público anterior aos zeros

Provar

```lean
NativeCarryC3Crosswalk.FiniteC3CompletedGreenWronskianSeam 1
```

usando o ledger completo, sem igualdade restrita a zeros.

### Gate A+ completado

Derivar, preferencialmente do mesmo teorema polarizado, a scalarização
xi-completada da fonte C3 canônica. Essa etapa liga diretamente a geometria à
Weyl que alimenta os momentos.

### Gate B: estado completado de duas variáveis

Construir um estado Hilbert local e provar

```text
completedGreenWronskian F Psi z w
  = (z - conj w) * inner (state w) (state z).
```

Depois ligar seus jets normalizados à recorrência de momentos e às incidências
TFVD/BR2. Isso fecha positividade estrita em toda ordem sem medida de zeros.

### Gate C: operador Jacobi infinito

Partir do core algébrico `J_0` e provar uma das duas rotas:

```text
closure(J_0) = B† B
```

ou

```text
closure(J_0) = operator induced by the exact infinite Jacobi matrix.
```

Em seguida provar que as apresentações coincidem e que `J` é positivo,
autoadjunto, limitado e injetivo.

### Gate D: operador de alturas

Usar cálculo funcional para definir `T = J^(-1/2)`, provar convergência forte
de resolventes das aproximações finitas e identificar o espectro por meio da
função característica/Weyl já derivada.

Uma rota geométrica alternativa é formar o Dirac supersimétrico do fator
fechado,

```text
D = [[0, B†], [B, 0]],
```

provar sua autoadjunção e então estudar `D^(-1)`. Essa rota é promissora porque
`D^2` contém `B†B`, mas ainda é uma proposta, não um teorema do grafo atual.

## Conclusão operacional

O material atual não pede um novo operador nem uma nova ideia espectral. Pede
que apresentações já construídas sejam identificadas por mapas tipados:

```text
completed TFVD/C3 ledger
  -> public diagonal Green seam
  -> completed Green/Cauchy scalarization
  -> two-variable moment Gram kernel
  -> positive infinite Jacobi operator
  -> inverse-square-root height operator.
```

O seam público fecha diretamente o confinamento. As etapas posteriores
formalizam a mesma resposta como um operador de alturas infinito; elas não
devem ser usadas como atalho circular para provar o confinamento.

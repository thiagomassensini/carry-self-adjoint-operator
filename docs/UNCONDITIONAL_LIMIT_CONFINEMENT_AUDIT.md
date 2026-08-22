# Auditoria do confinamento incondicional e do limite do operador de alturas

## Snapshot

- `native-carry-c3-crosswalk`: `1e9e06e1d51d176a909c187828f7c880e5d1207d`
- `carry-self-adjoint-operator`, base empilhada PR #6: `cd7c28551a98ab87a5fe45a27a07f2874de65c6e`
- probe vermelho isolado: PR #8, commit `78bcf666a718f2f7deebf969976da0cc5ef37b58`
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

As lacunas não são vagas. Elas se separam em três costuras tipadas.

## 1. Confinamento: uma única scalarização diagonal

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

### Composição kernel-checkable

O arquivo `UnconditionalLimitConfinementProbe.lean` prova:

```text
CanonicalCompletedC3GammaCauchyScalarizationSeam
  -> FinalGenuineZeroConfinement
```

A costura restante é exatamente

```lean
HasCanonicalCompletedNativeGammaCauchyScalarization
  canonicalCompletedC3SixCameraSource
```

isto é, para todo parâmetro não real,

```text
completed Green Wronskian
  = -2 i * concrete all-bases Cauchy skew.
```

Pela identidade gamma já provada, o lado direito é também

```text
(z - conj z) * positive gamma energy.
```

### Probe vermelho

O PR #8 conserva uma declaração deliberadamente incompleta que pede ao kernel
que construa essa scalarização sem premissa nova. Seu erro é evidência do
primeiro objetivo não habitado pelo grafo atual, não uma biblioteca candidata
a merge.

### Guardrail de não circularidade

Não basta provar a igualdade somente sob a hipótese de zero. O repositório já
mostra que uma scalarização restrita aos zeros tem a força do próprio
confinamento. O teorema válido precisa ser funcional, construído antes de
qualquer zero.

Também não se pode igualar o Wronskiano diagonal ao bulk C3 complexo cru: o
primeiro é puramente imaginário e o segundo retém parte real não nula fora da
meia-abscissa. A scalarização corretamente tipada usa a energia real positiva,
ou equivalentemente `-2 i` vezes a parte real do bulk fatorado.

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

### Ainda não provado

Esses objetos não são ainda um único operador infinito:

1. a matriz entrada a entrada não foi promovida a um `LinearPMap` ou a um
   operador limitado no Hilbert completado;
2. o fator Green fechado `B` ainda não foi promovido ao operador positivo
   autoadjunto `J = B† B`;
3. não há teorema identificando esse `J` com a matriz da torre e suas seções;
4. não foi provado `ker J = 0`;
5. não foi definido em Lean o cálculo funcional não limitado
   `T = J^(-1/2)` com seu domínio maximal;
6. não há ainda convergência forte de resolventes nem identificação de ausência
   de espectro extra.

É importante não tentar colar diretamente os `T_N`. O inverso da raiz
quadrada não preserva compressões principais em geral. A ordem correta é

```text
{J_N} -> J -> T = J^(-1/2) -> H = T direct_sum (-T).
```

O repositório `green-frame-theorem` já contém infraestrutura útil de
convergência forte do cálculo funcional contínuo para operadores limitados com
um intervalo espectral comum. Ela poderá ser reutilizada depois que o `J`
positivo limitado e injetivo for construído.

## Sequência mínima recomendada

### Gate A: scalarização anterior aos zeros

Provar uma instância concreta de

```lean
CanonicalCompletedC3GammaCauchyScalarizationSeam
```

ou, preferencialmente, uma identidade de duas variáveis mais forte da qual a
scalarização diagonal seja corolário.

### Gate B: estado completado de duas variáveis

Construir um estado Hilbert local e provar

```text
completedGreenWronskian F Psi z w
  = (z - conj w) * inner (state w) (state z).
```

Depois ligar seus jets normalizados à recorrência de momentos e às incidências
TFVD/BR2. Isso fecha positividade estrita em toda ordem sem medida de zeros.

### Gate C: operador Jacobi infinito

Definir o operador no core algébrico e provar uma das duas rotas equivalentes:

```text
J = B† B
```

ou

```text
J = operator induced by the exact infinite Jacobi matrix.
```

Em seguida provar que as duas apresentações coincidem, que `J` é positivo,
autoadjunto, limitado e injetivo.

### Gate D: operador de alturas

Usar cálculo funcional para definir `T = J^(-1/2)`, provar convergência forte
de resolventes das aproximações finitas e identificar o espectro por meio da
função característica/Weyl já derivada.

## Conclusão operacional

O material atual não pede um novo operador nem uma nova ideia espectral. Pede
que apresentações já construídas sejam identificadas por mapas tipados:

```text
completed TFVD/C3 ledger
  -> completed Green/Cauchy scalarization
  -> two-variable moment Gram kernel
  -> positive infinite Jacobi operator
  -> inverse-square-root height operator.
```

O primeiro elo é também o gate direto de confinamento. Os elos posteriores
formalizam o limite do operador, mas não precisam ser usados como atalho para
provar o confinamento.

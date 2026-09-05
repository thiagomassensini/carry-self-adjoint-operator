# BR2: calibração da fonte causal com retorno de bordo completo

Base desta rodada: `cbbd049a2f9ccffad691dd946c6241e36ae46cd1` (main, PR #52).

O resultado novo exclui uma família concreta: as respostas à fonte literal
C3/BR2, com qualquer par de sementes de bordo, na métrica vertical já existente.
Os dois readouts BR2 gerais continuam abertos. A positividade incondicional
de $\Delta_2$ permanece intacta.

## Tipos e objetos conferidos

Em `BR2CenterLegMomentKernel.lean`, o certificado existente tem os campos:

```lean
momentReadout : ∀ i j : ℕ ⊕ ℕ,
  (greenWronskianMomentKernel moments i j : ℂ) =
    scalarKernel (incidence.centerCoordinate i) (incidence.legCoordinate j)

greenOffDiagonalReadout : ∀ i j : ℕ ⊕ ℕ,
  incidence.centerCoordinate i ≠ incidence.legCoordinate j →
    scalarKernel (incidence.centerCoordinate i) (incidence.legCoordinate j) =
      inner ℂ (jet i) (jet j)
```

`BR2CameraIncidence.centerCoordinate_ne_legCoordinate` elimina a condição
geométrica. `BR2CenterLegGreenMomentCertificate.toComplexMomentKernel` combina
os dois readouts, e `.hankelPair_posSemidef` entrega ambos os Hankels para todo
$N$. Essas declarações foram reutilizadas; nenhum novo certificado foi criado.

O candidato testado é o que `BR2CausalGreenResponseTransport.lean` já constrói:

$$x_j=G_q b_j+R_q\beta_j,\qquad q=1/\sqrt3,\qquad\beta_j\in\mathbb C^2.$$

Aqui $b_j$ é `br2CameraBracketVerticalState 3 1 j`, $G_q$ é
`carryVerticalL2WeightedGreen`, e $R_q$ é `carryWeightedVerticalReturn`.
As duas pernas, o centro e o retorno inteiro são mantidos. A família indexada
por incidências ainda não está identificada com derivadas na altura nativa.

## Resultado formal novo

Arquivo: `CarrySelfAdjointOperator/BR2CausalBoundaryMetricCalibration.lean`.

O teorema existente
`carryWeightedVerticalCenteredBracket_br2CausalGreenResponseWithBoundary`
dá $B_qx_j=b_j$ para **qualquer** $\beta_j$. No centro exclusivo:

$$B_qx_j(3(j+1))=-2.$$

Para todo $x$ no mesmo $\ell^2$, provamos

$$|B_qx(n+1)|\le(q^{-1}+2+q)\|x\|.$$

Como $q^{-1}+2+q<5$ no valor canônico (usamos a cota não estrita $\le5$),

$$\|x_j\|\ge\frac25,\qquad\|x_j\|^2\ge\frac4{25}.$$

Reutilizando `canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth`,
segue a margem estrita, sem ajuste de coeficientes:

$$\boxed{\|x_j\|^2-h_0>\frac{39}{400}.}$$

O quadrado é da norma de **$G_qb_j+R_q\beta_j$**, depois da soma. Assim, a
estimativa já inclui ambos os cruzamentos; ela não soma energias como se os
dois vetores fossem ortogonais. O bordo pode variar livremente com a ordem.

Teoremas principais:

- `br2C3SourceSolution_nativeMassDefect_gt`: vale para qualquer solução da
  equação de fonte, sem hipótese sobre suas sementes.
- `canonicalBR2C3CausalResponseWithBoundary_nativeMassDefect_gt`: instancia a
  resposta completa já construída.
- `not_nonempty_canonicalBR2C3BoundaryResponse_momentCertificate`: nenhum
  `BR2CenterLegGreenMomentCertificate` nativo existe para essa família na
  métrica atual, qualquer que seja a incidência do certificado e o bordo por ordem.

O último teorema usa apenas a entrada `(Sum.inl 0, Sum.inl 0)` de
`.toComplexMomentKernel`, que exigiria $\|x_0\|^2=h_0$.

## Primeiro termo que não pode cancelar

Também provamos a condição necessária exata para qualquer candidato $x$ com
energia central correta. A assinatura Lean é:

```lean
theorem nativeMassCalibratedState_br2C3CenterSourceDefect_ne_zero
    (index : ℕ) (x : CarryVerticalL2)
    (hmass : ‖x‖ ^ 2 = canonicalCompletedNativeLogDerivativeMoment 0) :
    carryWeightedVerticalCenteredBracket
        (canonicalBR2CarryAmplitudeRatio 3) x (alignedCenter 3 index) + 2 ≠ 0
```

`hmass` é a propriedade necessária de um candidato, não uma realização nativa
postulada. Não há goal não resolvido no módulo: a igualdade com a fonte literal
foi refutada. A assinatura acima localiza o desacordo em uma coordenada.

## Alcance para a próxima tentativa

O resultado anterior `not_br2C3CausalResponse_coefficientEquation`, em
`ProjectiveValveCarryGreenObstruction.lean`, trata das respostas com sementes
nulas e usa invariância por translação. Esta rodada cobre sementes arbitrárias
e usa a equação local da fonte. Não reprova o argumento de translação.

Isso não exclui o certificado BR2 genérico, o kernel completado, uma métrica de
retorno diferente ou um transporte demonstrado que altere a fonte. Tampouco
identifica a fonte de incidência com a fonte Gamma. Não foram omitidos canais
do estado nativo para montar uma realização alternativa.

Antes de tentar usar essa família como jets nativos, a próxima ponte precisa
explicitar como o transporte muda a fonte e a métrica: o coeficiente central
literal $-2$ não pode permanecer com o mesmo $q$ e a mesma norma vertical se a
energia desejada é $h_0$. Ajustar somente as sementes é insuficiente.

O teste do bloco $G_2$ e do complemento de Schur continua necessário para um
candidato que passe pela entrada central. Para a família acima, o desacordo
já ocorre nessa primeira entrada; $\Delta_2>0$ não é usado para excluí-la.

## Auditoria e integração

O novo módulo não altera momentos, operadores, Jacobi, Gamma, pins ou toolchain.
O audit dedicado imprime os axiomas de todas as oito novas declarações e é
importado pelos audits BR2, geral e de construção de kernels. O aggregator
principal importa o módulo matemático.

Evidências desta rodada ficam em `research/br2-causal-boundary-2026-09-05/`.
O estado final das verificações está em `validation.txt`; os logs preservam a
saída do Lean. Esta rodada é mantida em branch separada enquanto os readouts
nativos gerais permanecem abertos.

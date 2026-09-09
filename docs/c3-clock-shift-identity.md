# Identidade de deslocamento: relógio C3, jets de altura e resposta causal

Base: `9cd2d14074bfe92cc48130fad973c83c539577e5`, na sequência da investigação
BR2 sobre `cbbd049a2f9ccffad691dd946c6241e36ae46cd1` (main, PR #52).
Branch desta rodada: `agent/c3-clock-shift-identity`.

## Resultado

A identidade investigada é

$$\langle u_p,u_{q+1}\rangle=\langle u_{p+1},u_q\rangle.$$

Ela foi provada para as potências do **relógio material C3 existente**, na
forma positiva induzida pela reconstrução dos quatro valores nodais, com a
semente mantida. Para a **família causal BR2 existente**, foi calculado um
defeito estritamente negativo já em $(p,q)=(0,1)$. Os **coeficientes de Taylor
na altura real** obedecem a uma terceira fórmula, com sinal e fatoriais.

Todas essas afirmações estão verificadas no Lean. Nenhuma delas identifica
o Gram com os momentos logarítmicos nativos em toda ordem.

## 1. Origem, mapa, destino e igualdade

Origem: `nativeC3BlockGradient m s` e sua semente
`positiveDirichletValue s (3*m)`, já utilizados por
`C3DynamicCompletedGreenForm.lean`.

Mapa: a reconstrução exata

$$R(f,g_0,g_1,g_2)=
(f,\ f+g_0,\ f+g_0+g_1,\ f+g_0+g_1+g_2).$$

Destino: os quatro valores nativos nos índices materiais
$3m+1,3m+2,3m+3,3m+4$, em `EuclideanSpace ℂ (Fin 4)`.

O relógio material $L$ é o `gradientClock` já existente, incluindo seu termo
afim de semente. O empacotamento `seededClock` apenas mantém também a evolução
da própria semente. Com as quatro frequências reais $d,a,b,c$, provamos

$$R(Lx)_i=\lambda_i R(x)_i,
\qquad(\lambda_0,\lambda_1,\lambda_2,\lambda_3)=(d,a,b,c).$$

Para os dados nativos, as frequências são exatamente os quatro logaritmos
materiais. `seededClock_nativeBlockSeededData_snd` identifica sua segunda
componente com `nativeC3BlockDynamicLogJet`, por igualdade definicional;
`seededClock_nativeBlockSeededData_fst` identifica a primeira com o valor
logarítmico nativo. Não foi introduzido outro operador espectral.

O produto interno é tomado **depois** da reconstrução. Portanto inclui os
cruzamentos entre semente e gradientes, e entre os gradientes. A reconstrução
é injetiva (`seededRecover_injective`).

O teorema `inner_seededRecover_clock_iterate` prova, inclusive para dois estados
iniciais diferentes,

$$\langle R(L^p x),R(L^q y)\rangle
=\sum_{i=0}^3\overline{R(x)_i}\,R(y)_i\lambda_i^{p+q}.$$

Daí `seededClock_inner_shift` entrega a identidade solicitada. A especialização
nativa, sem hipótese matemática adicional, é:

```lean
theorem nativeSeededC3Clock_inner_shift (m : ℕ) (s : ℂ) (p q : ℕ) :
    let L := seededClock (Real.log (3*m+1 : ℕ)) (Real.log (3*m+2 : ℕ))
      (Real.log (3*m+3 : ℕ)) (Real.log (3*m+4 : ℕ))
    let x := nativeBlockSeededData m s
    inner ℂ (seededRecover (L^[p] x)) (seededRecover (L^[q + 1] x)) =
      inner ℂ (seededRecover (L^[p + 1] x)) (seededRecover (L^[q] x))
```

Namespace: `CarrySelfAdjointOperator.C3TraceDynamics`.
Arquivo: `C3SeededClockShiftIdentity.lean`.
Vale para todo bloco completo e todas as ordens; não afirma independência
infinita dentro de um bloco de quatro coordenadas.

## 2. A altura real traz fase e fatorial

As potências materiais anteriores não são os coeficientes normalizados de
Taylor na altura. Mantivemos a convenção efetiva do repositório:

$$\tau_n=\frac{(-i)^n}{n!}R(L^n x).$$

`nativeSeededClockTaylorCoefficient_slope_eq` prova que, no estado crítico,
as três diferenças consecutivas dessas coordenadas são **exatamente**
`nativeDirichletSlopeTaylorCoefficient n (3*m+i.val)`. Essa declaração já
existia em `CompletedNativeTfvdCoefficientJets.lean`, junto da convergência
das diferenças finitas para os coeficientes.

Sem reprovar esse limite, o novo teorema
`seededClockTaylorCoefficient_weighted_inner_shift` calcula a identidade certa:

$$\boxed{(q+1)\langle\tau_p,\tau_{q+1}\rangle
=-(p+1)\langle\tau_{p+1},\tau_q\rangle.}$$

O sinal vem da conjugação de $-i$ no primeiro argumento do produto interno.
Os fatores vêm dos fatoriais. A relação é provada com dois estados iniciais
arbitrários, preservando a polarização.

Isso resolve a contabilidade de fase nesta camada finita. Não transforma
automaticamente a energia do relógio no kernel da log derivada completada.
Não se identificou altura com parâmetro de resolvente.

Arquivo: `C3SeededClockTaylorTransport.lean`.

## 3. Primeiro termo que falha na realização causal atual

Aqui $u_n$ significa precisamente
`br2CameraBracketCausalGreenResponse q 3 1 n`, com $0<q<1$.

Reutilizamos as identidades já existentes:

- `br2C3CausalResponse_succ_eq_shift`;
- `carryVerticalL2UnilateralShift_inner`;
- `br2CameraBracketCausalGreenResponseIncidenceJetTransport` e sua
  `even_linearIndependent`.

As duas primeiras fixam a mesma energia em $u_0,u_1,u_2$. A última garante
$u_0\ne u_2$. A identidade de norma da diferença fornece o resultado novo:

$$\boxed{\operatorname{Re}\bigl(
\langle u_0,u_2\rangle-\langle u_1,u_1\rangle\bigr)
=-\frac12\|u_0-u_2\|^2<0.}$$

Teoremas:

- `br2C3CausalResponse_firstShiftDefect_eq`;
- `br2C3CausalResponse_firstShiftDefect_neg`;
- `br2C3CausalResponse_firstShift_ne`.

O mapa projetivo já construído desfaz a mudança de coordenadas antes de aplicar
o Green causal. Usando `projectiveIncidenceRawJet_canonicalCarryGreen`, o teorema
`ProjectiveValve.canonicalProjectiveCarryGreen_firstShiftDefect_neg` transporta
a desigualdade ao mapa canônico, com $q$ derivado da geometria de carry.

A igualdade necessária que foi **refutada**, copiada com os objetos atuais, é:

```lean
projectiveIncidenceCoefficient (canonicalProjectiveCarryGreenMap 3) 3 1 0 2 =
  projectiveIncidenceCoefficient (canonicalProjectiveCarryGreenMap 3) 3 1 1 1
```

Não se trata de um goal ainda sem prova: a diferença tem parte real estritamente
negativa. O no-go se refere à família causal de sementes nulas que possui essa
lei de translação. A obstrução anterior para sementes arbitrárias, por massa
central, permanece em `BR2CausalBoundaryMetricCalibration.lean`.

Arquivo novo: `BR2CausalShiftDefect.lean`.

## 4. Por que a identidade verdadeira ainda não fecha o Gram nativo

A realização nodal da seção 1 retém a semente unitária no primeiro bloco.
`nativeBlockSeededData_zero_energy_ge_one` prova

$$\|R(\texttt{nativeBlockSeededData}\ 0\ s)\|^2\ge1.$$

Reutilizando `canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth`,
`nativeBlockSeededData_zero_energy_ne_nativeMoment` prova que essa energia
difere de $h_0$. Nenhuma constante foi ajustada para tentar fazer a massa bater.

O teste verdadeiro no relógio material e o teste falso na resposta causal
tratam de famílias e métricas explicitamente diferentes. Não se trocou uma
pela outra no certificado BR2. O cálculo de bloco completo não afirma um
teorema novo sobre limite de cutoffs nem remove caudas da característica.

O gate já existente continua sendo
`projectiveIncidenceMomentEquation_iff_boundary_transport`:

```lean
ProjectiveIncidenceMomentEquation moments T base radius ↔
  (∀ p, projectiveIncidenceCoefficient T base radius p 0 =
    oddMomentResponseCoefficient moments (p + 1)) ∧
  (∀ p q, projectiveIncidenceCoefficient T base radius p (q + 1) =
    projectiveIncidenceCoefficient T base radius (p + 1) q)
```

Para a construção causal canônica, a segunda condição é falsa. Para a forma
nodal do relógio, a identidade material é verdadeira, mas a normalização
nativa já falha no início. Esta rodada não fornece os dois readouts BR2 nem
usa esse gate como hipótese para anunciar um certificado HP.

## 5. Integração e validação

Os quatro módulos matemáticos novos são integrados pelo aggregator. O novo
`C3ClockShiftAudit.lean` imprime os axiomas das 24 novas declarações; é importado
pelos audits de observabilidade, fronteira projetiva, kernels, BR2 e geral.
Os dois registries correspondentes foram atualizados.

Nenhuma hipótese matemática nova foi acrescentada à teoria. As condições
$0<q<1$ do lema causal são satisfeitas pelo valor canônico já existente.
Não há mudança de pins, mathlib, toolchain, momentos, Jacobi ou Gamma.

Evidências reproduzíveis: `research/c3-clock-shift-2026-09-05/`.
`validation.txt` registra o resultado final do workflow completo e do exame
dos axiomas. O trabalho permanece em branch separada enquanto a identificação
Gamma/Gram nativo permanece aberta.

## 6. Cruzamento com os arquivos enviados durante a rodada

Foram inventariados os 20 arquivos Lean indicados em Downloads. Nove são
idênticos, byte a byte, aos módulos matemáticos atuais; entre eles estão
`ReturnMetricPolarizedKernel`, os quatro `PositiveObservable*`,
`CarryTfvdTraceMetricKernel`, a calibração C3 e os dois módulos de resíduos.
Os hashes e os caminhos comparados estão em
`research/c3-clock-shift-2026-09-05/supplied-source-comparison.json`.

As cópias de audits e de parte dos bridges têm diferenças em relação aos
arquivos consumidos hoje. As declarações `finiteStencil_add_cutoff` e
`not_exists_strong_limit_normalizedLiteralFiniteCameraStencil`, presentes nas
cópias locais indicadas, não foram localizadas na busca dirigida nos módulos
do projeto e nos pins C3/Weyl atuais. Não se apresentou essas duas cópias como
novos teoremas integrados nem se alterou pin para importá-las.

| Peças enviadas | O que fornecem para esta identidade |
|---|---|
| `ReturnMetricPolarizedKernel` | `polarizedCovariance_eq_direct` já cancela exatamente a métrica de retorno, para duas pernas arbitrárias. A forma que sobra é `C L Rᴴ Cᴴ`; a câmera é a mesma nas duas pernas. A especialização resolvente recebe as equações de resolvente e a simetria hermitiana. |
| `PositiveObservableParityKernel` | `inner_positiveObservableOrbit` já dá o Gram por soma das ordens, para uma fonte fixa e um observável cuja simetria é uma hipótese explícita. Não foi reprovido esse resultado genérico nem construído outro observável espectral. O novo resultado C3 calcula a forma sobre o relógio e a semente efetivos. |
| `PositiveObservableKernelSeries` e `PositiveObservableKernelDiagonal` | Entregam série, diagonal e `dslope` do readout do próprio observável, com suas condições de domínio. Não identificam esse readout com a característica nativa por coincidência de parâmetros. |
| `PositiveObservableNativeMomentBridge` | Localiza exatamente a equação escalar restante em `positiveObservableNativeConvolutionDefect`. O teorema de identificação recebe o anulamento desse defeito em todas as ordens; ele não o demonstra para uma nova fonte. |
| `CarryTfvdTraceMetricKernel` | Foi instanciado na resposta causal concreta nesta rodada. O resultado completo está abaixo. |
| `FiniteCanonicalCameraReadout`, `FiniteEnrichedCameraState`, `CanonicalNaimarkStateReadout` | Coisometria, Parseval, reconstrução e leitura coerente preservam informação e produtos internos nos respectivos domínios. Conservar também o canal invisível impede concluir uma redução de energia por descartar esse canal. |
| `C3ProjectiveHilbertRBBridge` | A igualdade `nativeGpreTfvdProjectivePulledBackInner_realization` preserva literalmente o produto interno do estado realizado. Foi instanciada no defeito causal, sem reconstruir o bridge. |
| `C3ProjectiveCompletedJetBridge` | `c3CompletedIteratedJet_cutoff_invariant` e o readout head+tail conservam exatamente os jets completados. Esta rodada não repete o limite nem substitui o readout completado por um prefixo. |
| `ExactCutoffCameraGram`, refinamento e escape de stencils | Tratam de cutoffs, resíduos de câmera e ambiente do limite. O Gram periódico de câmeras não é identificado com o Hankel nativo nesses resultados. As cópias locais e o pin atual foram distinguidos. |
| `C3TwoVariableGreenGamma` | A passagem Wronskiano → Gram recebe a identidade Green com os mesmos estados. A igualdade de sewing ainda precisa ser fornecida para aplicar a passagem ao kernel nativo. |
| `AtomicLogDerivativeResidue`, `CompletedNativeAtomicMultiplicity` | Fixam resíduos e multiplicidades analíticas nas condições declaradas. Não foram usadas hipóteses sobre zeros ou massas atômicas para fabricar a realização Gram. |

### Teste novo: a métrica TFVD pronta

No quarto módulo, `BR2CausalTfvdMetricShift.lean`, usamos diretamente
`carryTfvdMetricState`. Para a mesma família causal $u_n$, provamos primeiro
que seus dois valores de entrada são zero, e então calculamos seu trace:

$$\operatorname{Tr}_q u_n=0.$$

O teorema `br2C3CausalTfvdMetric_inner_eq_source` reutiliza, nesta ordem,

1. `carryTfvdMetricState_inner`;
2. `carryTfvdCausalSecondDifference_inner_eq_bracket_add_trace`;
3. `carryWeightedVerticalCenteredBracket_br2CausalGreenResponse`;
4. o trace calculado em `br2C3CausalResponse_trace_zero`.

O resultado é a igualdade polarizada completa

$$\langle V_q(u_i),V_q(u_j)\rangle=\langle b_i,b_j\rangle,$$

onde $V_q$ é o mapa TFVD já definido e $b_i$ a fonte de incidência original.
Reutilizando `c3_rawCoefficient_zero_two` e `c3_rawCoefficient_one_one`, segue:

```lean
theorem br2C3CausalTfvdMetric_firstShiftDefect_eq_neg_six
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    let v := fun n => carryTfvdMetricState q (br2CameraBracketCausalGreenResponse q 3 1 n)
    inner ℂ (v 0) (v 2) - inner ℂ (v 1) (v 1) = -6
```

Assim, essa métrica pronta conserva a informação causal, mas não satisfaz
a identidade Hankel nessa família. O trace foi avaliado, não apagado.

Já `br2C3CausalProjectiveReturn_firstShiftDefect_neg` aplica a recuperação
Hilbert/RB pronta aos mesmos vetores e transporta o defeito estritamente
negativo da seção 3. Nenhuma nova norma de retorno foi escolhida.

### Como as cinco notas orientam o diagnóstico

`01_retorno_sondas.md` descreve a identidade polarizada hoje formalizada em
`ReturnMetricPolarizedKernel`; a câmera e a fonte fixas fazem parte da conta.
`02_modo_misto_vandermonde.md` distingue os momentos do observável compacto
dos momentos logarítmicos, e conserva a identificação nativa como obrigação.
`03_cumulantes_bordo.md` distingue a convolução da primeira coluna do transporte
entre ordens. Essas são justamente as duas condições do gate já existente.

`IDENTIDADE_PROJETIVA_EXATA_LIMITE_OPERADOR_ALTURAS` identifica o Wronskiano
escalar e a compatibilidade da torre, condicionando a realização positiva ao
Gram correspondente. Não foi usado o Hankel positivo de toda ordem como
premissa. `C2_GREEN_HAAR_RIGGED_VECTOR_PORT_REPORT` mantém o canal coarse e os
setores ocultos, com diferenças de tipos ainda registradas; seus diagnósticos
históricos não foram transformados em proibições gerais.

O achado verificável desta comparação é o teste acima sobre dois mapas já
existentes. Nenhum dos mapas testados forneceu a identificação nativa que falta.
Isso não exclui um sewing do trace completado que envolva outra relação
demonstrada entre fonte, dinâmica e forma de Green.

## Validação final desta rodada

- `lake build --wfail CarrySelfAdjointOperator.C3ClockShiftAudit`: passou.
- `bash scripts/audit.sh`: passou nas 15 etapas, terminando em `kernel audit passed`.
- 24 teoremas novos auditados; todas as 6.037 entradas de axiomas impressas
  pelo workflow (incluindo repetições) usam somente o conjunto padrão.
- Axiomas de `nativeSeededC3Clock_inner_shift`,
  `br2C3CausalResponse_firstShiftDefect_eq` e
  `br2C3CausalTfvdMetric_firstShiftDefect_eq_neg_six`:
  `[propext, Classical.choice, Quot.sound]`.
- Os novos módulos não têm goals não resolvidos. A igualdade causal necessária
  foi refutada; a realização Gamma/Gram nativa geral continua aberta.
- Pins, configuração Lake, mathlib e toolchain preservados.

Os logs e o `validation.txt` da pasta de evidências registram os comandos e
o exame dos axiomas. Não foi feito merge nesta rodada.

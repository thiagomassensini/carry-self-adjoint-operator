# Comutador relacional e conexão logarítmica finita

Investigação e formalização realizadas no `ssh llm`, em
`/home/thlinux/carry-self-adjoint-operator`, a partir de
`79871d2455fa05862a22a4afaedb1f6ab306524a`. O HEAD local e origin/main
coincidiam; não havia mudanças posteriores ao checkpoint. Os dois untracked
C2OddTfvdTransport preexistentes foram preservados. Nenhum pin/toolchain,
métrica ou definição anterior foi alterado. Nenhum worktree novo foi criado.

## Resultado e status dos checkpoints

| Checkpoint | Status real | Limitação |
|---|---|---|
| PASS_LOG_GAP_COMMUTATOR_DECOMPOSITION | PROVADO | Todas as ordens/dimensões finitas do candidato U; arestas de seus índices de coordenadas, não novos Green ports |
| PASS_SEEDED_MATERIAL_CLOCK_TRANSPORT | PROVADO | Equivalência linear finita, operador explícito de arestas, C3 local e seed + TFVD convergentes em ordem fixa; nenhuma unitariedade ou inversa infinita |
| PASS_MATERIAL_CHIRAL_ENRICHED_SEWING | NÃO OBTIDO | Falta a correspondência geométrica independente entre posição material e nó/ordem radial, com completion e bordo |
| OPEN_SOURCE_BOUNDARY_POSITIVITY_ALL_ORDER | ABERTO | A energia original permanece assinada; nilpotência e Gram físico não a positivam |

Três módulos novos contêm 31 teoremas públicos e 10 definições públicas.
As definições são interfaces necessárias: linearização fiel de U, peso de
aresta, matriz/estado do defeito, prefixo, equivalência, operador explícito e
síntese original das duas pernas. Reutilizamos os samples físicos existentes
`finiteDirichletSamples`, os clocks, o gradiente, os carriers e a forma quiral;
não criamos aliases dos resultados históricos nem outro relógio radial.

## Domínios, contradomínios e índices

| Objeto | Tipo efetivo | Índices / norm / orientação |
|---|---|---|
| `sourceCoordinateEnd n k` | End ℂ do `FiniteRealSpectralHilbert (2*n)` | Exatamente `sourceCoordinateInput`; apenas uma interface linear, sem nova normalização |
| `finiteMaterialClock N`, `materialJet r` | End ℂ do Hilbert nodal finito N | posição j+1, frequência real log(j+1), tempo/derivada permanecem distintos |
| `logEdgePowerWeight q r` | ℂ | q→q+1, `positiveLogGap q=log(q+2)-log(q+1)`; polinômio de ordem r |
| `sourceEdgeContribution` / `sourceEdgeState` | coordenada / Hilbert de 2n | inclui U_(i,a), fases, amplitude completada, fatores de diferença e todos os a posteriores |
| `materialSeedGradientEquiv N` | Hilbert(N+1) ≃ₗ ℂ × Hilbert(N) | seed x₀, Δx_q=x_(q+1)-x_q; somente equivalência linear |
| `seededMaterialJet N r` | End ℂ do produto existente ℂ × Hilbert(N) | fórmula explícita de produto e reconstrução; norm de produto não declarado unitário |
| `sourceRadialPair n k` | Hilbert(2n) →ₗ carrier projetivo quiral existente | duas sínteses originais incident/returned, com mesmos coeficientes |
| `canonicalCompletedNativeProjectiveChiralForm` | dois pares quirais → ℂ | conjuga a primeira entrada; `1/2*(inner incident-inner returned)` |
| Seed + TFVD enriquecido | ℂ × carrier enriquecido TFVD existente | limite em cutoff para cada ordem fixa; ordinário/log já têm `WithLp 2`; sem estado nodal infinito |

```text
Hilbert nodal(N+1) ── O_N(x)=(x0, Δx) ──► ℂ × Hilbert de arestas(N)
         │ L^r                                  │ seededMaterialJet N r
         ▼                                      ▼
Hilbert nodal(N+1) ───────── O_N ──────────► ℂ × Hilbert de arestas(N)

O_N^-1(s,d)_j = s + prefix_j(d)           (finito; isometria não afirmada)
```

```text
x ── L^r ──► L^r x ── U ──► U L^r x ── Γ=(Incident,Returned) ──► J(L^r x)
│                                 = L^r Ux + D_r x
└── U ──► Ux ── L^r ──► L^r Ux                 │
                                                └ D_r = soma vetorial de arestas
J(L^r x) = Γ(L^r Ux) + Γ(D_r x)       (ambas as pernas preservadas)
```

O segundo diagrama é do **candidato de coordenadas**. Não identifica um índice
radial com uma posição material física. Γ é a fonte original, não o embedding
Green/Parseval do carrier material; igualdade entre esses dois mapas não foi
demonstrada.

## I. Identidade de potência e matriz literal

Provamos, sem hipótese U L=L U, para os operadores existentes:

```text
U L^r - L^r U = sum_(j=0..r-1) L^j (U L-L U) L^(r-1-j).
```

`sourceCoordinateEnd_commutator_power` cobre r=0 (soma vazia e operador zero)
e r=1 (um único termo). A interface linear `sourceCoordinateEnd` tem a mesma
função que U; a conversão aplica as leis lineares da matriz original. Não
utilizamos uma conjugação U L U^-1, nem regularidade ou positividade.

`sourceCoordinateEnd_commutator_apply` identifica sua ação exatamente com a
matriz `logCommutatorMatrix n k r`:

```text
C^(r)_(i,a) = U_(i,a) * (ell_a^r-ell_i^r).
```

Esse C^(r) indica ordem de jet, **não** potência de C^(1). A nilpotência abaixo
usa a potência matricial `(C^(r))^(2n)`, mantendo essas ordens separadas.

## II. Caminhos de arestas e fluxo de contribuições

Primeiro, independentemente de U e da fonte, provamos:

```text
w(q,r) = g_q * sum_(m=0..r-1) ell_(q+1)^(r-1-m) * ell_q^m
       = ell_(q+1)^r-ell_q^r,
ell_a^r-ell_i^r = sum_(q=i..a-1) w(q,r)          se i<=a.
```

O segundo resultado é telescópico e cobre r=0; o primeiro reutiliza o
polinômio geométrico de potência. Para r=1, w(q,1)=g_q. Nenhum sinal foi
invertido para ajustar o operador. As amplitudes complexas continuam dentro
de U: a positividade real de um log-gap não assina essa amplitude nem a energia.

Demonstramos `sourceInputMatrix_zero_below`: U_(i,a)=0 se a<i. Isso vem
literalmente de `completedGreenForwardWeight a i`, pois `choose(a,i)=0`.
Somente depois usamos esse suporte para decompor o comutador.

```text
([U,L^r]x)_i = sum_a sum_(q=i..a-1) w(q,r) * U_(i,a) * x_a
            = sum_q w(q,r) * S_(q,i)(x),
S_(q,i)(x) = sum_a [i<=q<a] * U_(i,a) * x_a.
```

As somas são finitas e a reordenação foi provada. A API usa q:Fin(2n);
o termo terminal q=2n-1 é vazio pela condição q<a e a<2n. Assim as arestas
efetivas são exatamente q=i,...,2n-2. `sourceEdgeContribution` é uma soma de
contribuições, não um fluxo físico ou Green port já identificado. O estado
`sourceEdgeState` retém todas as coordenadas de destino antes da síntese.

Essa decomposição e a identidade operatorial de potência descrevem o mesmo
comutador, por duas provas independentes: telescopia escalar nas coordenadas
e telescopia não comutativa no anel de endomorfismos. A igualdade de ação
`sourceCoordinateEnd_commutator_apply` fixa sua compatibilidade.

## III. Suporte estrito, nilpotência e canários 2/4/6

O fator de diferença zera a diagonal. A matriz do comutador é estritamente
triangular superior: C_(i,a)=0 para a<=i. Provamos por indução que a potência
matricial t só pode receber caminhos com a>=i+t; daí `(C^(r))^(2n)=0`,
para todos n,k,r, sem esperar regularidade eventual. É um resultado do modelo
finito exato, não cancelamento da forma assinada nem um resultado de operador
infinito.

| Dimensão | Parâmetros do teorema geral | Primeira contribuição na ordem 1 | Nilpotência certificada |
|---|---|---|---|
| 2 | n=1, r=1 | `C_(0,1)=-A0*h_k^-1*log(2)` | C²=0 |
| 4 | n=2, r=1 | mesmo coeficiente, demais ordens retidas | C⁴=0 |
| 6 | n=3, r=1 | mesmo coeficiente, demais ordens retidas | C⁶=0 |

`logCommutatorMatrix_first_edge` vale em toda dimensão par positiva;
`...first_edge_ne_zero` prova não nulidade sob regularidade explícita de F e
HB no primeiro nó. A regularidade eventual existente fornece canários
eventuais; não usamos native_decide ou experimentos para esses resultados.
A entrada (0,1) atua sobre o segundo vetor de base material. A primeira
obstrução de dimensão 2 é recuperada literalmente, sem ajustar A0 ou h_k.
Para r=0 todos os defeitos desaparecem como potência identidade, o que não
certifica a origem física das coordenadas.

## IV. Seed + gradiente e relógio explícito

`material_sample_reconstruction` prova, para **todo** vetor finito:

```text
x_j = x_0 + sum_(q<j) Δx_q.
```

`materialSeedGradientEquiv` constrói a equivalência linear com inversa
explícita; não é apenas uma injetividade. A orientação coincide com
`finiteMaterialGradient`. A prova não impõe norma no produto nem diz que a
equivalência é unitária.

A regra vetorial all-order é:

```text
Δ(L^r x)_q = ell_q^r * Δx_q + w(q,r)*x_(q+1).
```

Substituindo a reconstrução, definimos **pela fórmula**:

```text
seededMaterialJet N r (s,d):
  s' = ell_0^r*s,
  d'_q = ell_q^r*d_q + w(q,r)*(s + sum_(j<=q) d_j).
```

Só depois provamos o entrelaçamento com O_N. A lei aditiva de ordens e a
igualdade `seededMaterialJet N r = seededMaterialJet N 1 ^ r` decorrem da
equivalência e dos jets materiais existentes. r=0 é identidade; r=1 tem
seed transformado zero porque ell_0=log(1)=0. Isso não apaga a influência do
seed: quando d=0, a fórmula de arestas contém g_q*s. O relógio pode matar
um canal nodal enquanto sua diferença reaparece nas arestas.

## V. Crosswalk C3, Green e TFVD

Não criamos outro vetor de samples: `finiteDirichletSamples` é o objeto
físico existente, cujo índice j representa j+1. Provamos que:

- seu gradiente finito coincide com `positiveDirichletGradient s q`;
- o gradiente após o relógio coincide com `positiveLogDirichletGradient s q`;
- para **duas entradas independentes** z,w, o wedge das arestas consecutivas
  desses vetores é a soma dos dois `canonicalC3AdjacentClockChannels` existentes.

As duas versões de Leibniz locais são portanto a mesma regra de produto
vetorial após a mudança **tipada** para os samples Dirichlet. O wedge C3 é
bilinear, não o pairing quiral sesquilinear; nenhuma conjugação foi inserida
para identificar os dois. No pairing quiral, Mathlib conjuga a primeira
entrada, como já preservado na expansão da fonte.

Reutilizamos, sem aliases, `canonicalC3Sample_eq_seed_add_gradientPrefix` e
`canonicalC3AdjacentClockReturn_eq_seededPrefix`: os endpoints dos dois
retornos leem exatamente seed + prefixos de gradientes. A nova inversa vale
para todos os vetores finitos; esses teoremas são sua instanciação nos samples.
`canonicalC3MixedPrefixGreenProvenance_clockTransport` mantém ambos os
canais e o port Green subtraído. `...Head_clockTransport` mantém também
crosses ordenados e resíduos; `adjacentMaterialLogGap_decomposition` e
`...Return_eq_symmetric_add_imbalance` continuam separando os dois produtos
complexos. Não eliminamos nenhum desses retornos ou resíduos.

O crosswalk demonstrado é local/finito nos carriers existentes. Não prova
que as arestas dos **índices de U** sejam essas arestas materiais C3.

## VI. Defeito transportado pelas duas pernas e identidade assinada

Γ=`sourceRadialPair` é literalmente a síntese incident/returned original,
com o mesmo vetor de coeficientes. No candidato de coordenadas:

```text
D_r x = U L^r x - L^r Ux = sum_q w(q,r) • sourceEdgeState(q,x)
Γ(D_r x) = sum_q w(q,r) • Γ(sourceEdgeState(q,x))
J(L^r x) = Γ(L^r Ux) + Γ(D_r x).
```

A identidade é de **estados completos**. Amplitudes completadas, fases,
grid e fatoriais vivem no U original; ambas as sínteses usam os estados
radiais originais. Não redefinimos U nem a segunda perna a partir da primeira.

Para entradas independentes x,y e ordens r,s, escrevendo Bx=Γ(L^r Ux),
Dx=Γ(D_r x), e similarmente para y:

```text
form(J(L^r x),J(L^s y)) =
  form(Bx,By) + form(Bx,Dy) + form(Dx,By) + form(Dx,Dy).
```

Todos os crosses são preservados. `form` é a forma quiral original
`1/2*(inner incident-inner returned)`; Q=4*Re(form) é exatamente
`2*(norm incident²-norm returned²)`. Não substituímos sua diferença por
soma de normas, não postulamos sinal de qualquer defeito e não a igualamos
ao Gram físico material positivo. O resultado permanece dentro do candidato
de coordenadas; a passagem Γ↔Green/TFVD físico ainda precisa de proveniência.

## VII. Limite, seed e canais complementares

`criticalMaterialTaylor_seed` preserva a fase/fatorial `(-I)^r/r!` e prova
que o seed material crítico é 1 na ordem zero e 0 nas ordens positivas.
`criticalSeededTfvdTaylor_tendsto` e `...EnrichedTaylor_tendsto` acrescentam
esse seed como uma coordenada separada às convergências TFVD existentes.
O segundo mantém ambos os canais ordinário/log, com suas normalizações
anteriores. São limites em cutoff para cada ordem fixa, no produto de
carriers existentes; não uma renormalização do Hilbert nodal.

O no-go `finiteParsevalMaterialEmbedding_critical_no_limit` permanece intacto.
Uma observação seed + slopes pode convergir enquanto sua reconstrução
nodal não converge nesse Hilbert: as inversas finitas não fornecem uma
inversa infinita limitada. Nenhum limite radial k, dimensão 2n e cutoff N
foi trocado. Nenhuma uniformidade nas inversas, no chart U ou no sinal foi
deduzida. O seed bruto preservado aqui não é automaticamente o seed da
fonte analiticamente completada; seus complementos ainda precisam ser
transportados independentemente.

## Gate mínimo restante

`OPEN_MATERIAL_TO_COMPLETED_CHIRAL_SOURCE_SEWING` agora requer identificar,
por geometria independente, os caminhos de coordenadas radiais de U com os
canais materiais/seed/slopes/Green/TFVD, incluindo completion, restos,
quadraturas e retorno de bordo. A álgebra das arestas e o transporte Γ do
defeito já estão demonstrados. Falta o mapa de proveniência entre carriers,
com domínio e controle necessários. O antigo no-go para apagar o seed
continua pertinente. `PASS_MATERIAL_CHIRAL_ENRICHED_SEWING` não foi concedido.

O gate de positividade estrita da fonte all-order continua independente.
Não usamos HP, Hankel positiva, medida ajustada, whitening ou métricas novas.

## Verificação e publicação

As 41 declarações estão no registry global e no guard dedicado
`LogGapConnectionAudit`; o checker exige cobertura exata dos três módulos.
Os builds focalizados usam `--wfail`, com `#print axioms` de todas as declarações.
O README START HERE contém os checkpoints e links para os módulos e este
relatório. Logs, resultado da auditoria oficial, commits e main final são
registrados no checkpoint de entrega após concluir as verificações.

## Assinaturas dos 31 teoremas públicos novos

Namespace `CarrySelfAdjointOperator.LogGapConnection`.

### RelationalLogGapCommutator

```lean
theorem sourceCoordinateEnd_commutator_power (n k r : ℕ) :
    sourceCoordinateEnd n k * finiteMaterialClock (2*n)^r -
      finiteMaterialClock (2*n)^r * sourceCoordinateEnd n k =
      ∑ j ∈ Finset.range r,
        finiteMaterialClock (2*n)^j *
          (sourceCoordinateEnd n k * finiteMaterialClock (2*n) -
            finiteMaterialClock (2*n) * sourceCoordinateEnd n k) *
          finiteMaterialClock (2*n)^(r-1-j)

theorem logEdgePowerWeight_eq_difference (q r : ℕ) :
    logEdgePowerWeight q r =
      positiveLogVertexWeight (q+1)^r - positiveLogVertexWeight q^r

theorem logPower_difference_eq_edgeSum (i a r : ℕ) (hia : i ≤ a) :
    positiveLogVertexWeight a^r - positiveLogVertexWeight i^r =
      ∑ q ∈ Finset.Ico i a, logEdgePowerWeight q r

theorem sourceInputMatrix_zero_below {n k : ℕ} (i a : Fin (2*n)) (ha : a.val < i.val) :
    nativeSourceChiralJetInputMatrix n k i a = 0

theorem sourceCoordinateEnd_commutator_apply (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) (i : Fin (2*n)) :
    ((sourceCoordinateEnd n k * finiteMaterialClock (2*n)^r -
        finiteMaterialClock (2*n)^r * sourceCoordinateEnd n k) x) i =
      (logCommutatorMatrix n k r).mulVec (fun a => x a) i

theorem logCommutatorMatrix_diagonal (n k r : ℕ) (i : Fin (2*n)) :
    logCommutatorMatrix n k r i i = 0

theorem logCommutatorMatrix_strict_support {n k r : ℕ} (i a : Fin (2*n))
    (ha : a.val ≤ i.val) : logCommutatorMatrix n k r i a = 0

theorem sourceCoordinateInput_commutator_edgeSum (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) (i : Fin (2*n)) :
    sourceCoordinateInput n k (materialJet r x) i -
      materialJet r (sourceCoordinateInput n k x) i =
      ∑ a : Fin (2*n), ∑ q ∈ Finset.Ico i.val a.val,
        logEdgePowerWeight q r * nativeSourceChiralJetInputMatrix n k i a * x a

theorem sourceCoordinateInput_commutator_edgeFlux (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) (i : Fin (2*n)) :
    sourceCoordinateInput n k (materialJet r x) i -
      materialJet r (sourceCoordinateInput n k x) i =
      ∑ q : Fin (2*n), logEdgePowerWeight q.val r * sourceEdgeContribution n k x q i

theorem logCommutatorMatrix_first_edge (n k : ℕ) (hn : 0 < n) :
    logCommutatorMatrix n k 1 ⟨0, by omega⟩ ⟨1, by omega⟩ =
      -completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹ * (Real.log 2 : ℂ)

theorem logCommutatorMatrix_first_edge_ne_zero (n k : ℕ) (hn : 0 < n)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0)
    (hHB : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0) :
    logCommutatorMatrix n k 1 ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ 0

theorem logCommutatorMatrix_nilpotent (n k r : ℕ) :
    logCommutatorMatrix n k r ^ (2*n) = 0

```

### SeededMaterialLogConnection

```lean
theorem edgePrefix_succ {N : ℕ} (d : FiniteRealSpectralHilbert N) (j : Fin N) :
    edgePrefix d (j.val+1) = edgePrefix d j.val + d j

theorem material_sample_reconstruction {N : ℕ} (x : FiniteRealSpectralHilbert (N+1))
    (j : Fin (N+1)) : x j = x 0 + edgePrefix (finiteMaterialGradient N x) j.val

theorem materialGradient_jet_productRule {N : ℕ} (r : ℕ)
    (x : FiniteRealSpectralHilbert (N+1)) (q : Fin N) :
    finiteMaterialGradient N (materialJet r x) q =
      positiveLogVertexWeight q.val^r * finiteMaterialGradient N x q +
        logEdgePowerWeight q.val r * x q.succ

theorem seededMaterialJet_intertwines (N r : ℕ)
    (x : FiniteRealSpectralHilbert (N+1)) :
    materialSeedGradientEquiv N (materialJet r x) =
      seededMaterialJet N r (materialSeedGradientEquiv N x)

theorem seededMaterialJet_zero (N : ℕ) : seededMaterialJet N 0 = 1

theorem seededMaterialJet_add_order (N r s : ℕ) :
    seededMaterialJet N r * seededMaterialJet N s = seededMaterialJet N (r+s)

theorem seededMaterialJet_eq_clock_power (N r : ℕ) :
    seededMaterialJet N r = seededMaterialJet N 1 ^ r

theorem seededMaterialClock_seed (N : ℕ) (y : ℂ × FiniteRealSpectralHilbert N) :
    (seededMaterialJet N 1 y).1 = 0

theorem materialGradient_clock_right_productRule {N : ℕ}
    (x : FiniteRealSpectralHilbert (N+1)) (q : Fin N) :
    finiteMaterialGradient N (materialJet 1 x) q =
      positiveLogVertexWeight (q.val+1) * finiteMaterialGradient N x q +
        positiveLogGap q.val * x q.castSucc

theorem finiteDirichletSamples_gradient (N : ℕ) (s : ℂ) (q : Fin N) :
    finiteMaterialGradient N (finiteDirichletSamples (N+1) s) q = positiveDirichletGradient s q.val

theorem finiteDirichletSamples_clockGradient (N : ℕ) (s : ℂ) (q : Fin N) :
    finiteMaterialGradient N (materialJet 1 (finiteDirichletSamples (N+1) s)) q =
      positiveLogDirichletGradient s q.val

theorem finiteDirichletSamples_mixedAdjacentClock (N : ℕ) (z w : ℂ) (q : Fin N) :
    sameSEdgeBoundaryWedge
      (finiteMaterialGradient (N+1) (finiteDirichletSamples (N+2) w) q.castSucc)
      (finiteMaterialGradient (N+1) (finiteDirichletSamples (N+2) w) q.succ)
      (finiteMaterialGradient (N+1) (materialJet 1 (finiteDirichletSamples (N+2) z)) q.castSucc)
      (finiteMaterialGradient (N+1) (materialJet 1 (finiteDirichletSamples (N+2) z)) q.succ) =
      (canonicalC3AdjacentClockChannels z w q.val).1 +
        (canonicalC3AdjacentClockChannels z w q.val).2

theorem criticalMaterialTaylor_seed (N r : ℕ) :
    ((-Complex.I)^r / (r.factorial : ℂ)) *
      materialJet r (finiteDirichletSamples (N+1) (1/2)) 0 =
        if r = 0 then (1 : ℂ) else 0

theorem criticalSeededTfvdTaylor_tendsto (r : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((-Complex.I)^r / (r.factorial : ℂ)) *
          materialJet r (finiteDirichletSamples (N+1) (1/2)) 0,
         materialTfvdTaylorPrefix N r))
      Filter.atTop (nhds (if r = 0 then (1 : ℂ) else 0,
        canonicalCompletedNativeTfvdTaylorCoefficientState r))

theorem criticalSeededTfvdEnrichedTaylor_tendsto (r : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((-Complex.I)^r / (r.factorial : ℂ)) *
          materialJet r (finiteDirichletSamples (N+1) (1/2)) 0,
         materialTfvdEnrichedTaylorPrefix N r))
      Filter.atTop (nhds (if r = 0 then (1 : ℂ) else 0,
        canonicalCompletedNativeTfvdEnrichedTaylorRawJet r))

```

### ChiralLogGapDefectTransport

```lean
theorem sourceCoordinateJetDefect_eq_edgeSynthesis (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceCoordinateJetDefect n k r x =
      ∑ q : Fin (2*n), logEdgePowerWeight q.val r • sourceEdgeState n k x q

theorem sourceRadialPair_defect_eq_edgeSynthesis (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceRadialPair n k (sourceCoordinateJetDefect n k r x) =
      ∑ q : Fin (2*n), logEdgePowerWeight q.val r •
        sourceRadialPair n k (sourceEdgeState n k x q)

theorem sourceCoordinatePair_jet_eq_base_add_defect (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceCoordinatePair n k (materialJet r x) =
      sourceRadialPair n k (materialJet r (sourceCoordinateInput n k x)) +
        sourceRadialPair n k (sourceCoordinateJetDefect n k r x)

theorem sourceCoordinatePair_jet_signed_defect_expansion (n k r s : ℕ)
    (x y : FiniteRealSpectralHilbert (2*n)) :
    let Bx := sourceRadialPair n k (materialJet r (sourceCoordinateInput n k x))
    let By := sourceRadialPair n k (materialJet s (sourceCoordinateInput n k y))
    let Dx := sourceRadialPair n k (sourceCoordinateJetDefect n k r x)
    let Dy := sourceRadialPair n k (sourceCoordinateJetDefect n k s y)
    canonicalCompletedNativeProjectiveChiralForm
      (sourceCoordinatePair n k (materialJet r x))
      (sourceCoordinatePair n k (materialJet s y)) =
      canonicalCompletedNativeProjectiveChiralForm Bx By +
        canonicalCompletedNativeProjectiveChiralForm Bx Dy +
        canonicalCompletedNativeProjectiveChiralForm Dx By +
        canonicalCompletedNativeProjectiveChiralForm Dx Dy

```

## Evidências completas de validação no llm

- Target `ChiralLogGapDefectTransport` com pré-requisitos: passou com `--wfail` (9692 jobs).
- Target `LogGapConnectionAudit`: passou com `--wfail` (9693 jobs), incluindo os três resultados adicionais de seed/limite.
- Todas as 41 declarações públicas (31 teoremas, 10 defs) passaram pelo guard dedicado e `#print axioms`; somente `propext`, `Classical.choice`, `Quot.sound`.
- `bash scripts/static_audit.sh`: passou, incluindo os três checkers de cobertura; nenhum trust escape.
- `bash scripts/audit.sh`: passou; root, Audit, BR2Audit, OrderAudit, RecoveredC2GreenAudit e os audits oficiais anteriores; terminou em `kernel audit passed`.
- `git diff --check`: passou. Links relativos do START HERE verificados e história abaixo dele preservada integralmente.
- Nenhum linter foi desabilitado. Não foram usados experimentos numéricos: canários 2/4/6 são especializações dos teoremas gerais exatos.

Logs integrais: `/tmp/log-gap-axioms.log`, `/tmp/log-gap-full-audit.log`. Publicação, commits e main são confirmados no checkpoint final abaixo.

## Integração confirmada

[PR #67](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/67) MERGED por procedimento normal em `2a7840e6257512925f436cf9ad02e3a749bf232f`.
Commit científico validado: `223cf24828e0cd6c2a45859543f64bffa2f1e0f1`. Main local e origin/main confirmadas no merge; ancestralidade e diff vazio dos módulos Lean, scripts, registros e pins verificados. O commit documental seguinte somente registra esse estado no índice.

Runs Actions 38091661128 e 38091655602 terminaram em startup_failure. A API confirmou zero jobs no primeiro; gh run view aponta possível problema de workflow, sem diagnóstico específico. Não inferimos billing nem falha Lean, nem declaramos Actions aprovadas. Nenhuma proteção foi contornada.

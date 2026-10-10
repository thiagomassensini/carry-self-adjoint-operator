# Síntese multibase e transporte material all-order

## Resultado científico e fronteira

Há um transporte dinâmico finito fiel dos vetores materiais literais para o
Green State existente e sua análise Parseval, usando o relógio logarítmico
original. Todas as ordens, câmeras, seeds e brackets sobrevivem como vetores.
A frequência material também é reconstruída do ledger multibase existente:
log(n)^r é a síntese de todos os words ordenados de suas contribuições
relacionais, com multiplicidades e produtos cruzados preservados.
O pairing misto depende de r+s. O Gram físico de ordem zero é o Gram periódico
linear em M mais um defeito físico explícito, não uma igualdade assintótica
reescrita como exata.

Há também uma costura vetorial independente entre os samples Dirichlet
clockados e os coeficientes TFVD ordinários/logarítmicos all-order. A operação
necessária é tomar a diferença material depois da ação do relógio, com a fase
(-i)^r e o factorial já impostos pela fonte. O par de canais converge em l2
para os vetores TFVD existentes, em cada ordem fixa.

Esses resultados não identificam o Gram positivo dos vetores físicos nem o
Gram desses coeficientes TFVD com o kernel de momentos da característica
completada. A fonte projetiva/quiral tem uma forma assinada e normalizações
analíticas adicionais. Não foi definido um segundo pairing por referência ao
primeiro, nem um D_material-source com normalizações incompatíveis.

Dois no-gos novos tornam a fronteira explícita: a realização nodal fiel da
amplitude crítica não possui limite Hilbert no Green Parseval; a diferença
material sozinha não é injetiva. Retendo o seed e todas as diferenças, a
observação finita é injetiva.

## Proveniência: fontes consultadas antes da implementação

Todos os builds e a pesquisa foram executados via `ssh llm`. Não houve
mudança de pins, toolchains ou arquivos não relacionados.

| Repositório | HEAD/estado inicial | Uso |
|---|---|---|
| carry-self-adjoint-operator | main `1645a7c439efe909158d451402ce9408267d1a6e`; dois arquivos C2OddTfvdTransport não rastreados preexistentes | alvo principal; preservados os dois arquivos |
| native-carry-spectral-weyl | PR #15 aberto, HEAD `871217099a069083791738578b2e44005b31986e`; main `248249ce098491f4194209d8e698dc5965f1405d` | fatoração relacional consultada; não importada por alteração de pin |
| geometry-of-numbers | main `e1084b43533255b399b82dc307b536d7dfdca07f` | AGENTS e relógios/obstruções finitos consultados; sem alterações |
| primos | branch `agent/release-v0.63.0-c3-carrier-gate`, HEAD `8c4b7fdf65a49d1d0febe8193d56e2cfb2191260`, ahead 5; CPFormal.lean dirty e um arquivo não rastreado | estado observado e preservado; implementação usa o pin existente |

O alvo não possui AGENTS.md próprio nem em seus ancestrais verificados.
As regras de geometry-of-numbers foram respeitadas; nenhum módulo Foundation
foi alterado. Não foram criadas worktrees nesta tarefa.

Pins do alvo: Lean v4.32.0; NativeCarryC3Crosswalk
`150cfc7fb08da96bf8117f15869cc2b819d593c2`; geometry-of-numbers
`d7cc54f5c485320f1fada33118e9e6101488819a`; Weyl transitivo
`298d83c9351e308a5213b9f5ac32e44087f98a9f`; CPFormal transitivo
`65d50f6db1208708e109982ba97e1d51d3039956`; Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`.

O PR #15 não está no pin do autoadjunto nem integrado à main. Sua CI anterior
foi bloqueada antes de executar qualquer step por problema de billing da conta.
O resultado relacional é uma fonte de comparação separada; este PR usa os
mesmos objetos Gram já existentes no pin, sem copiar aquele módulo nem forçar
integração externa.

## Tabela de objetos e transportes realmente disponíveis

Escreva N=finiteFamilyWindow M camera. Label b, cutoff M, posição material
n+1, edge n, profundidade C2 e ordem r são índices diferentes.

| Objeto Lean | Tipo/domínio → contradomínio | Métrica/cutoff | Transporte disponível |
|---|---|---|---|
| `FiniteClockJets.finiteMaterialClock N` | `Module.End ℂ (FiniteRealSpectralHilbert N)` | Hilbert Euclidiano complexo; log(n+1); todos N | simetria em CPFormal; sem nova diagonal |
| `FiniteClockJets.finiteMaterialOrbit N t` | equivalência linear isométrica do mesmo Hilbert | fase exp(-it log(n+1)) | `finiteMaterialClockJet_eq_generatorPow`; gerador forte -iL |
| `finiteLiteralCameraMatrix M camera` | `Matrix ι (Fin N) ℝ` | coeficientes brutos, sem amplitude e sem divisão por M | row Gram literal; limite normalizado comprovado |
| novo `literalCameraVector M camera b` | `FiniteRealSpectralHilbert N` | mesma linha literal, complexificada sem normalização | pairing zero = `literalFiniteCameraGram` |
| `FormalStencil` / `finiteStencil b M` | `ℕ →₀ ℤ` | suporte geométrico material; seed mais centers | `finiteStencil_apply`; stencil não tem uma métrica inventada |
| novo `stencilMaterialAction x` | stencil → linear sobre ℤ → Hilbert material de x | conserva todas as coordenadas da janela | seed/center/radius/fiber como identidades vetoriais |
| `c2AlignedIndexCore`, `c2AlignedIndexDepth` | índice alinhado j → naturais | endereço C2; não é ordem r | alignedCenter = 2^depth * core; não generalizado silenciosamente |
| novos `RelationalLogVoice n`, `RelationalLogWord n r` | suporte finito de vozes e funções Fin r → suporte | carrier algébrico, sem nova métrica; eixo de voz distinto do perfil b | products de todas as contribuições e síntese exatamente igual a L^r |
| novo `materialJetTower M camera r` | submódulo do Hilbert material N | span de L^j v_b, j≤r | L envia a torre inteira para a próxima |
| `GreenStateMaterialLog.greenStateMaterialLogGenerator` | `State →ₗ.[ℂ] State` | domínio logarítmico maximal existente | ação log(n) e self-adjointness; domínio é verificado |
| novo `finiteGreenMaterialEmbedding N` | Hilbert N → linear ℂ → `GreenFrame.Concrete.State` | inclusão nodal finita isométrica | domínio e intertwining vetorial reais |
| `GreenParsevalMaterialLog.greenParsevalAnalysis` | State → contínuo linear ℂ → `ConcreteAnalysisSpace` | análise Parseval canônica, range fechado | A* A=I; operador de range mais zero no complemento |
| novo `finiteParsevalMaterialEmbedding N` | Hilbert N → linear ℂ → ConcreteAnalysisSpace | sem métrica nova | inclusão seguida da análise existente; todos os jet steps |
| novo `finiteMaterialGradient N` | Hilbert (N+1) → linear ℂ → Hilbert N | diferenças x(n+2)-x(n+1) | kernel contém constantes; seed + gradient injetivo |
| `canonicalCompletedNativeTfvdTaylorCoefficientState r` | `CarryVerticalL2` | l2 existente no índice material de slopes; r fixo | prefixos convergem, majorante de slopes já provado |
| `canonicalCompletedNativeTfvdEnrichedTaylorRawJet r` | `WithLp 2 (CarryVerticalL2 × CarryVerticalL2)` | canais ordinário e logarítmico, fase/factorial canônicos | novo prefixo material converge vetorialmente para esse par |
| `canonicalCompletedTfvdGreenAllCutoffNaimarkRawJet M k r` | `RealifiedNaimarkComplexification` | cutoff M, passo k e ordem r separados | convergência em M para cada k,r; limite em k tem gate próprio |
| `nativeSourceProjectiveBoundaryJetSynthesis n k x` | `Fin(2n)→ℂ` → carrier projetivo/quiral | forma assinada; duas pernas mantidas | energy control para cada n fixo e eta>0, eventualmente em k |
| `ChiralReturn.radialEulerPowerSynthesis k N m d` | `Fin N→ℂ` → Cauchy carrier existente | grid radial; Euler order m, não log material | Green alternado com conjugação e todos os crosses |
| `normalizedCompletedNativeCameraCharacteristic b M` | função ℝ→ℂ | cabeça + tail exatos; factor removido, completion mantida | universalidade dos jets normalizados; não realiza por si um vetor físico comum |

### Hipóteses e normalizações auditadas

`completedNativeCameraUniversality` é incondicional para câmeras suportadas
b≥2, mas refere-se à função normalizada com tail exato. A igualdade
`completedNativeCameraLogDerivativeMoment_eq_canonical` decorre dos
coeficientes dessa função. `completedNativeCamera_finiteJacobi_independent`
mantém explicitamente suas hipóteses de Hankel PosDef; altura mantém também
Jacobi PosDef. Nenhuma delas foi inferida da universalidade.

`c2CenterStencil_eval_logPower_eq_fiberAllOrderBracket` e
`c2FiniteCamera_allOrderReadout_eq_seed_add_fiberBracketSum` preservam a
convenção alinhada C2. O novo crosswalk conserva primeiro a identidade de
stencils/vetores; só depois identifica cada observável logarítmico existente.
`c2Tower_logPower_criticalAmplitude_eq_stirling_newtonJet` refere-se ao k
vertical de uma torre C2, não ao clockOrder r de um sample n+1.

`ChiralReturn.radialEulerPower_green_boundary` tem conjugação no primeiro
argumento, fator k+1 e soma alternada de crosses ordenados. Não é um quadrado
positivo. `storage_one_eq_odd_green_tower_and_remainder` requer F e a coordenada
HB positiva não nulos nos pontos radiais, mantém o fator 4 no pairing com o
resto e não afirma sinal desse resto.

`nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control` e
`storage_one_chiralJetInput_eventually_energy_control` controlam a energia
original assinada uniformemente nas direções de um n fixo. Não fornecem
controle uniforme simultâneo em todas as dimensões nem substituem storage por
uma norma positiva. O chart quiral existente conserva as duas quadraturas.

Em geometry-of-numbers, `finiteSeedGradientClock` é transporte pela
equivalência de seed/gradient, linear mas não unitária na norma de produto
padrão. `finiteCompletedGreenIntertwiner_clock` transporta a reconstrução
nodal finita ao Green real. `SeparatedCenterClockObstruction` exclui uma
família injetiva de intertwiners para o bloco central limitado fixo quando
log(n) ultrapassa sua norma. Esses resultados foram consultados no checkout
atual; não foram promovidos a imports novos no pin antigo.

## Construção e identidades novas

### Origem relacional all-order do relógio

O módulo `RelationalMaterialClockAllOrder` reutiliza
`cameraLogContributionVectorComplex`, `cameraComplexSynthesis` e o teorema
`primeDepthLogLedger_eq_log`. O crosswalk existente de multiplicidade para
profundidade posicional justifica a interpretação dessas vozes; não se altera
retroativamente a torre geométrica para defini-la por factorization.

Para cada n positivo e r, o carrier preserva cada word ordenado de comprimento
r no suporte relacional de n. `relationalLogWord_synthesis` prova

`log(n)^r = sum_word product_j cameraLogContributionVectorComplex n (word j)`.

O caso n=1 e a ordem r=0 permanecem literais: suporte vazio, único word vazio
em ordem zero, produto 1. Nenhuma câmera privilegiada é escolhida.
`relationalWordJetSynthesis_eq_materialJet` identifica a síntese completa
com o clock original, coordenada por coordenada. A máscara de cada câmera
física atua sobre todos os words, com o mesmo coeficiente literal, antes da
síntese final (`relationalWordJet_cameraMaterialAction`).

As vozes primas do ledger, os labels das câmeras físicas e as resoluções
A_b(d) do Gram relacional são eixos distintos. Não se infere igualdade entre
seus kernels ou métricas. O kernel estático K sozinho não foi declarado como
uma definição da dinâmica; a proveniência adicional do relógio é o ledger
logarítmico já demonstrado pela geometria relacional.

### Torre física multibase

`materialJet r x = (finiteMaterialClock N)^r x` e
`materialJet_apply` dá log(n+1)^r x(n+1). Mathlib é conjugado-linear no primeiro
argumento. A realidade da diagonal e `IsSymmetric.pow` provam exatamente

`inner (L^r x) (L^s y) = inner x (L^(r+s) y)`.

`materialOrbit_derivative_eq_phasedJet` registra separadamente a derivada
temporal verdadeira: (-i)^r L^r x. Não se omite fase ou factorial ao passar a
coeficientes de Taylor.

`materialCameraSynthesis_jet_pairing` mantém todos os pares b,c com
`conj(a_b) z_c H_M^(r,s)(b,c)`. `materialJetGram_posSemidef` realiza a matriz
como V*V no Hilbert material existente. Essa PSD pertence à família física;
não certifica o Hankel da fonte completada.

`materialClock_maps_jetTower` prova L V^(r) ⊆ V^(r+1) sobre o span completo,
não apenas nos geradores. Não pressupõe invariância de V^(0) nem introduz uma
compressão que elimine o complemento.

### Ordem zero e defeito literal

`materialCameraPairing_zero_eq_literalGram` identifica a linha física bruta.
`materialCameraPairing_zero_eq_periodicGram_add_residue` e
`materialCameraPairing_six_zero_exact` dão

`H_M^(0,0)(b,c) = M G_420(b,c) + exactCutoffCameraGramResidue 420 M b c`.

O defeito é o centered core mais a soma física de bordo definidos previamente.
`materialCameraPairing_six_zero_tendsto` recupera o limite depois de dividir
por M. O contraexemplo kernel-checked
`materialCameraPairing_six_one_c2_defect` dá energia 7 para C2 no cutoff 1,
enquanto a entrada limite é 6: o defeito compatível é exatamente +1.

A relação K(d,e)=1/lcm(d,e) do PR #15 explica o mesmo Gram limite, incluindo
min(ell_b,ell_c) e todos os crosses. Não implica igualdade do Gram físico
bruto em cutoffs arbitrários.

### Brackets e transporte Green vetorial

`cameraMaterialJet_eq_seed_add_centerSum` é all-base e vetorial.
`cameraMaterialJet_eq_seed_add_radiusSum` inclui todo radiusSet, inclusive
o endpoint antipodal par. A C2 tem seu próprio theorem
`c2MaterialJet_eq_seed_add_fiberVectorSum`, obtido da identidade de endereço
com core/depth, e não de uma extrapolação ímpar.

`materialJet_dirichletSamples_apply` identifica os observáveis all-order
existentes coordenada a coordenada. O sampleState é um vetor finito antes de
qualquer leitura de câmera. Na utilização física de uma família, N é sua
janela comum inteira; as identidades algébricas também valem para prefixos
menores, onde stencilMaterialAction é explicitamente uma restrição.

`finiteGreenMaterialEmbedding_inner` prova a métrica da inclusão nodal.
Cada imagem está no domínio real do operador logarítmico. A promoção Parseval
conserva inner e satisfaz `finiteParsevalMaterialEmbedding_allOrder_step` em
qualquer ordem. `finiteParsevalMaterialEmbedding_camera_jet_synthesis` mantém
seed e centers sob essa promoção. São igualdades vetoriais efetivas entre
carriers, sem igualdade literal fictícia dos operadores em espaços diferentes.

### Costura TFVD all-order e canal perdido

`finiteMaterialTaylorGradient_apply` compara duas proveniências independentes:
de um lado L^r aplicado aos samples Dirichlet, seguido de diferença material;
do outro o `nativeDirichletSlopeTaylorCoefficient` já existente. O fator
(-i)^r/r! é o mesmo da fonte original.

`materialTfvdTaylorPrefix_eq_canonical` fecha a identidade vetorial em
CarryVerticalL2. `materialTfvdTaylorPrefix_tendsto` usa o majorante já provado
para slopes; `materialTfvdEnrichedTaylorPrefix_tendsto` conserva conjuntamente
o ordinário e o logarítmico com seu fator I(r+1). Os teoremas valem em cada
ordem natural arbitrária fixa; não afirmam norma uniforme em toda a torre.

`finiteMaterialGradient_not_injective` identifica o canal constante/seed
perdido. `finiteMaterial_seed_gradient_injective` prova que a observação
finita fica fiel ao guardar seed e todos os edges. Assim, a convergência do
gradient não é usada como prova de convergência do estado nodal completo.

## Obstruções e gates que permanecem

1. O span de seis perfis periódicos não é invariante pela segunda diferença
   do PR #15. Aqui se usa o relógio material e se aumenta a ordem da torre;
   aquele shift periódico não foi rebatizado como L.
2. O bloco central limitado tem o no-go de frequência mencionado acima.
   O novo transporte usa toda a janela nodal e o range Parseval existente.
3. `finiteParsevalMaterialEmbedding_critical_energy` calcula exatamente o
   prefixo harmônico da amplitude crítica, sem renormalização.
   `finiteParsevalMaterialEmbedding_critical_energy_tendsto` e
   `finiteParsevalMaterialEmbedding_critical_no_limit` provam a divergência e
   ausência de limite no carrier Green real dessa realização fiel.
4. O kernel quiral é uma diferença assinada. A PSD física e o limite TFVD
   raw não fecham seu contrato de positividade, cancelamento de bordo ou
   equivalência de momentos.

O gate mínimo para uma identificação com a fonte projetiva/quiral completada
é construir um mapa enriquecido de states material/seed/gradient/câmeras para
as duas pernas originais da fonte, demonstrar sua ação nos jets com as fases
e normalizações canônicas, e transportar a forma assinada com todos os
crosses, completion, return e restos. A fonte já possui
`nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource` e controles do
storage no chart próprio; falta ligar aquele chart ao carrier físico desta
torre. O novo mapa nodal → Green Parseval não é essa ligação.

Para projetores, a igualdade de Gram não demonstra os dois quadrados de
`NaimarkProjectorIntertwiningSeam`: readout e síntese ainda precisam de mapas
de estados e de coordenadas explicitamente compatíveis. A taxa de estabilidade
do projetor via C=B+E e gap singular continua uma questão separada; não foi
substituída por equivalência dinâmica.

Não foi alegado D_M^(r,s)=0 ou sinal de um defeito material/chiral cuja
comparabilidade ainda não está estabelecida. O defeito já comparável e fechado
é o residue físico de ordem zero; os termos quiral/tail permanecem em seus
carriers originais. Hankel, Jacobi, alturas e HP não são conclusões deste PR.

## Validação

Os cinco módulos novos têm 48 teoremas públicos, 18 definições públicas e
duas abreviações públicas.
A auditoria dedicada lista todas as 68 declarações com `#print axioms` e um
guard fundacional que só aceita propext, Classical.choice e Quot.sound.
O registro público existente foi estendido, e um checker verifica a cobertura
exata deste novo namespace. Root e Audit importam a superfície nova;
scripts/audit.sh executa sua auditoria antes do pacote completo.

O primeiro exemplo de energia C2 revelou que o simp default importava um
certificado upstream native_decide de radiusSet_two. A prova foi reescrita
por redução aritmética explícita para que esse axioma não entre na superfície
nova. Não foram mudados certificados ou pins históricos para esconder isso.

Comandos no llm, com `/home/thlinux/.elan/bin` no PATH:

```bash
lake build --wfail CarrySelfAdjointOperator.FiniteMaterialTfvdJetTransport
lake build --wfail CarrySelfAdjointOperator.FiniteMultibaseMaterialJetTransportAudit
lake env lean CarrySelfAdjointOperator/FiniteMultibaseMaterialJetTransportAudit.lean
python3 scripts/check_material_camera_jet_registry.py
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Resultado observado no llm: o target TFVD com seus pré-requisitos passou
(9157 jobs); a superfície relacional e a auditoria dedicada passaram
(9175 jobs); o build do root público passou (10088 jobs), seguido de Audit
(10227 jobs), BR2Audit, OrderAudit e RecoveredC2GreenAudit.
O script oficial terminou com `kernel audit passed`. O checker confirmou
68 declarações/48 teoremas e o guard explícito não encontrou axiomas fora
do conjunto fundacional permitido. O scan não encontrou trust escapes.
Os comandos com `--wfail` passaram, e `git diff --check` passou.
Mensagens informativas antigas de ring não são warnings.
O estado final da publicação é registrado na entrega. Não foram usados ajustes numéricos, fitting, novas métricas,
axiomas matemáticos ou positividade postulada. Experimentos numéricos novos
não foram necessários para essas identidades e no-gos.

## Assinaturas públicas novas

O apêndice abaixo é extraído das declarações Lean literais, sem os corpos das
provas. Namespace: `CarrySelfAdjointOperator.MaterialCameraJets`.

### FiniteMultibaseMaterialJetTower

```lean
theorem materialJet_apply {N : ℕ} (r : ℕ) (x : FiniteRealSpectralHilbert N) (n : Fin N) :
    materialJet r x n = (finiteRealSpectralFrequency n : ℂ) ^ r * x n

theorem materialJet_add_order {N : ℕ} (r s : ℕ) (x : FiniteRealSpectralHilbert N) :
    materialJet r (materialJet s x) = materialJet (r + s) x

theorem materialJet_pairing {N : ℕ} (r s : ℕ) (x y : FiniteRealSpectralHilbert N) :
    inner ℂ (materialJet r x) (materialJet s y) =
      inner ℂ x (materialJet (r + s) y)

theorem materialOrbit_derivative_eq_phasedJet {N : ℕ} (r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    iteratedDeriv r (fun t : ℝ => finiteMaterialOrbit N t x) 0 =
      (-Complex.I) ^ r • materialJet r x

theorem materialCameraSynthesis_jet_pairing {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r s : ℕ) (a z : ι → ℂ) :
    inner ℂ (materialJet r (materialCameraSynthesis M camera a))
      (materialJet s (materialCameraSynthesis M camera z)) =
      ∑ b, ∑ c, conj (a b) * z c * materialCameraPairing M camera r s b c

theorem materialJetGram_posSemidef {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) : (materialJetGram M camera r).PosSemidef

theorem materialCameraPairing_add_order {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r s : ℕ) (b c : ι) :
    materialCameraPairing M camera r s b c =
      materialCameraPairing M camera 0 (r + s) b c

theorem materialCameraPairing_eq_logWeightedSum {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r s : ℕ) (b c : ι) :
    materialCameraPairing M camera r s b c =
      ∑ n : Fin (finiteFamilyWindow M camera),
        ((finiteCoefficientAt (camera b) M n.val * finiteCoefficientAt (camera c) M n.val : ℝ) : ℂ) *
          (Real.log ((n.val + 1 : ℕ) : ℝ) : ℂ) ^ (r + s)

theorem materialCameraPairing_zero_eq_literalGram {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (hc : ∀ b, 2 ≤ camera b) (b c : ι) :
    materialCameraPairing M camera 0 0 b c =
      (literalFiniteCameraGram M (camera b) (camera c) : ℂ)

theorem materialCameraPairing_zero_eq_periodicGram_add_residue {ι : Type*} [Fintype ι]
    (M period : ℕ) (camera : ι → ℕ) (hc : ∀ b, 2 ≤ camera b) (b c : ι) :
    materialCameraPairing M camera 0 0 b c =
      ((M : ℝ) * periodicGramMatrix period camera b c +
        exactCutoffCameraGramResidue period M (camera b) (camera c) : ℝ)

theorem materialCameraPairing_six_zero_exact (M : ℕ) (b c : Fin 6) :
    materialCameraPairing M sixCamera 0 0 b c =
      ((M : ℝ) * sixCameraGram b c +
        exactCutoffCameraGramResidue 420 M (sixCamera b) (sixCamera c) : ℝ)

theorem materialCameraPairing_six_one_c2_defect :
    materialCameraPairing 1 sixCamera 0 0 0 0 = (sixCameraGram 0 0 : ℂ) + 1

theorem materialCameraPairing_six_zero_tendsto (b c : Fin 6) :
    Filter.Tendsto
      (fun M : ℕ => (M : ℂ)⁻¹ * materialCameraPairing M sixCamera 0 0 b c)
      Filter.atTop (nhds (sixCameraGram b c : ℂ))

theorem materialJetTower_mono {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) {r s : ℕ} (hrs : r ≤ s) :
    materialJetTower M camera r ≤ materialJetTower M camera s

theorem materialClock_maps_jetTower {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) :
    materialJetTower M camera r ≤
      (materialJetTower M camera (r + 1)).comap
        (finiteMaterialClock (finiteFamilyWindow M camera))

theorem materialJetFamily_energy_nonneg {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (r : ℕ) (a : ι × Fin (r+1) → ℂ) :
    0 ≤ (inner ℂ
      (∑ p : ι × Fin (r+1), a p • materialJet p.2.val (literalCameraVector M camera p.1))
      (∑ p : ι × Fin (r+1), a p • materialJet p.2.val (literalCameraVector M camera p.1))).re

```

### FiniteMultibaseMaterialBracketTransport

```lean
theorem cameraMaterialAction_apply {N : ℕ} (b M : ℕ)
    (x : FiniteRealSpectralHilbert N) (n : Fin N) :
    cameraMaterialAction b M x n = (finiteCoefficient b M (n.val + 1) : ℂ) * x n

theorem literalCameraVector_eq_stencilMaterialAction {ι : Type*} [Fintype ι]
    (M : ℕ) (camera : ι → ℕ) (b : ι) :
    literalCameraVector M camera b =
      cameraMaterialAction (camera b) M (WithLp.toLp 2 (fun _ => (1 : ℂ)))

theorem materialJet_stencilMaterialAction {N : ℕ} (r : ℕ)
    (x : FiniteRealSpectralHilbert N) (f : FormalStencil) :
    materialJet r (stencilMaterialAction x f) =
      stencilMaterialAction (materialJet r x) f

theorem cameraMaterialJet_eq_seed_add_centerSum {N : ℕ} (b M r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    materialJet r (cameraMaterialAction b M x) =
      stencilMaterialAction (materialJet r x) (seedStencil b) +
        ∑ j ∈ Finset.range M,
          stencilMaterialAction (materialJet r x) (centerStencil b j)

theorem cameraMaterialJet_eq_seed_add_radiusSum {N : ℕ} (b M r : ℕ)
    (hb : b ≠ 2) (x : FiniteRealSpectralHilbert N) :
    materialJet r (cameraMaterialAction b M x) =
      stencilMaterialAction (materialJet r x) (seedStencil b) +
        ∑ j ∈ Finset.range M, ∑ radius ∈ FiniteNativeCarryOperator.Camera.radiusSet b,
          stencilMaterialAction (materialJet r x)
            (centeredBracketStencil (FiniteNativeCarryOperator.Camera.alignedCenter b j) radius)

theorem c2MaterialJet_eq_seed_add_fiberVectorSum {N : ℕ} (M r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    materialJet r (cameraMaterialAction 2 M x) =
      stencilMaterialAction (materialJet r x) (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          stencilMaterialAction (materialJet r x)
            (centeredBracketStencil
              (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1)

theorem materialJet_dirichletSamples_apply (N r : ℕ) (s : ℂ) (n : Fin N) :
    materialJet r (finiteDirichletSamples N s) n =
      realLogPowerDirichletPower r s ((n.val + 1 : ℕ) : ℝ)

theorem cameraMaterialJet_dirichletSamples_apply (N b M r : ℕ) (s : ℂ) (n : Fin N) :
    materialJet r (cameraMaterialAction b M (finiteDirichletSamples N s)) n =
      (finiteCoefficient b M (n.val + 1) : ℂ) *
        realLogPowerDirichletPower r s ((n.val + 1 : ℕ) : ℝ)

theorem c2MaterialDirichletJet_eq_seed_add_fiberVectors (N M r : ℕ) :
    materialJet r (cameraMaterialAction 2 M (finiteDirichletSamples N (1/2))) =
      stencilMaterialAction (materialJet r (finiteDirichletSamples N (1/2))) (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          stencilMaterialAction (materialJet r (finiteDirichletSamples N (1/2)))
            (centeredBracketStencil
              (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1)

```

### FiniteMaterialCameraGreenTransport

```lean
theorem finiteGreenMaterialEmbedding_inner (N : ℕ) (x y : FiniteRealSpectralHilbert N) :
    inner ℂ (finiteGreenMaterialEmbedding N x) (finiteGreenMaterialEmbedding N y) =
      inner ℂ x y

theorem finiteGreenMaterialEmbedding_mem_domain (N : ℕ) (x : FiniteRealSpectralHilbert N) :
    finiteGreenMaterialEmbedding N x ∈ greenStateMaterialLogGenerator.domain

theorem finiteGreenMaterialEmbedding_clock (N : ℕ) (x : FiniteRealSpectralHilbert N) :
    greenStateMaterialLogGenerator
      ⟨finiteGreenMaterialEmbedding N x, finiteGreenMaterialEmbedding_mem_domain N x⟩ =
        finiteGreenMaterialEmbedding N (finiteMaterialClock N x)

theorem finiteParsevalMaterialEmbedding_inner (N : ℕ) (x y : FiniteRealSpectralHilbert N) :
    inner ℂ (finiteParsevalMaterialEmbedding N x) (finiteParsevalMaterialEmbedding N y) =
      inner ℂ x y

theorem finiteParsevalMaterialEmbedding_mem_domain (N : ℕ) (x : FiniteRealSpectralHilbert N) :
    finiteParsevalMaterialEmbedding N x ∈ greenParsevalMaterialLogOperator.domain

theorem finiteParsevalMaterialEmbedding_clock (N : ℕ) (x : FiniteRealSpectralHilbert N) :
    greenParsevalMaterialLogOperator
      ⟨finiteParsevalMaterialEmbedding N x, finiteParsevalMaterialEmbedding_mem_domain N x⟩ =
        finiteParsevalMaterialEmbedding N (finiteMaterialClock N x)

theorem finiteParsevalMaterialEmbedding_allOrder_step (N r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    greenParsevalMaterialLogOperator
      ⟨finiteParsevalMaterialEmbedding N (materialJet r x),
        finiteParsevalMaterialEmbedding_mem_domain N (materialJet r x)⟩ =
      finiteParsevalMaterialEmbedding N (materialJet (r + 1) x)

theorem finiteParsevalMaterialEmbedding_jet_pairing (N r s : ℕ)
    (x y : FiniteRealSpectralHilbert N) :
    inner ℂ (finiteParsevalMaterialEmbedding N (materialJet r x))
      (finiteParsevalMaterialEmbedding N (materialJet s y)) =
        inner ℂ x (materialJet (r + s) y)

theorem finiteParsevalMaterialEmbedding_camera_jet_synthesis (N b M r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    finiteParsevalMaterialEmbedding N (materialJet r (cameraMaterialAction b M x)) =
      finiteParsevalMaterialEmbedding N (stencilMaterialAction (materialJet r x) (NativeCarrySpectralWeyl.Camera.FiniteBridge.seedStencil b)) +
        ∑ j ∈ Finset.range M, finiteParsevalMaterialEmbedding N
          (stencilMaterialAction (materialJet r x) (NativeCarrySpectralWeyl.Camera.FiniteBridge.centerStencil b j))

theorem finiteParsevalMaterialEmbedding_critical_energy (N : ℕ) :
    ‖finiteParsevalMaterialEmbedding N (historicalInitialState N)‖^2 =
      ∑ j ∈ Finset.range N, ((j+1 : ℕ) : ℝ)⁻¹

theorem finiteParsevalMaterialEmbedding_critical_energy_tendsto :
    Filter.Tendsto
      (fun N => ‖finiteParsevalMaterialEmbedding N (historicalInitialState N)‖^2)
      Filter.atTop Filter.atTop

theorem finiteParsevalMaterialEmbedding_critical_no_limit :
    ¬ ∃ z : ConcreteAnalysisSpace,
      Filter.Tendsto (fun N => finiteParsevalMaterialEmbedding N (historicalInitialState N))
        Filter.atTop (nhds z)

```

### FiniteMaterialTfvdJetTransport

```lean
theorem finiteMaterialTaylorGradient_apply (N r : ℕ) (n : Fin N) :
    finiteMaterialTaylorGradient N r n = nativeDirichletSlopeTaylorCoefficient r n.val

theorem materialTfvdTaylorPrefix_eq_canonical (N r : ℕ) :
    materialTfvdTaylorPrefix N r =
      canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState r N

theorem materialTfvdTaylorPrefix_tendsto (r : ℕ) :
    Filter.Tendsto (fun N => materialTfvdTaylorPrefix N r) Filter.atTop
      (nhds (canonicalCompletedNativeTfvdTaylorCoefficientState r))

theorem materialTfvdEnrichedTaylorPrefix_tendsto (r : ℕ) :
    Filter.Tendsto (fun N => materialTfvdEnrichedTaylorPrefix N r) Filter.atTop
      (nhds (canonicalCompletedNativeTfvdEnrichedTaylorRawJet r))

theorem finiteMaterialGradient_not_injective (N : ℕ) :
    ¬ Function.Injective (finiteMaterialGradient N)

theorem finiteMaterial_seed_gradient_injective (N : ℕ) :
    Function.Injective (fun x : FiniteRealSpectralHilbert (N+1) =>
      (x 0, finiteMaterialGradient N x))

```

### RelationalMaterialClockAllOrder

```lean
theorem relationalLogVoice_synthesis {n : ℕ} (hn : n ≠ 0) :
    (∑ p : RelationalLogVoice n, cameraLogContributionVectorComplex n p.val) =
      (Real.log n : ℂ)

theorem relationalLogWord_synthesis {n : ℕ} (hn : n ≠ 0) (r : ℕ) :
    (∑ word : RelationalLogWord n r, relationalLogWordAmplitude n r word) =
      (Real.log n : ℂ)^r

theorem relationalWordJetSynthesis_eq_materialJet (N r : ℕ) (x : FiniteRealSpectralHilbert N) :
    relationalWordJetSynthesis N r (relationalWordJet r x) = materialJet r x

theorem relationalWordJet_cameraMaterialAction {N : ℕ} (b M r : ℕ)
    (x : FiniteRealSpectralHilbert N) (n : Fin N) (word : RelationalLogWord (n.val+1) r) :
    relationalWordJet r (cameraMaterialAction b M x) n word =
      (NativeCarrySpectralWeyl.Camera.FiniteBridge.finiteCoefficient b M (n.val+1) : ℂ) *
        relationalWordJet r x n word

theorem relationalCameraWordJet_synthesis {N : ℕ} (b M r : ℕ)
    (x : FiniteRealSpectralHilbert N) :
    relationalWordJetSynthesis N r (relationalWordJet r (cameraMaterialAction b M x)) =
      materialJet r (cameraMaterialAction b M x)

```

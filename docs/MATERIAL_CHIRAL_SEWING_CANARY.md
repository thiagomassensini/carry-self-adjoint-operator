# Costura Material–Quiral: auditoria tipada e canários

Checkpoint científico de 10/10/2026, executado exclusivamente no `ssh llm`,
`/home/thlinux/carry-self-adjoint-operator`. Regra: síntese completa antes do readout.

## Consolidação anterior

O PR #65 foi integrado por merge normal em
`0f6b063ef9cfa75f698b900bad277a3a04519110`, após reexecutar
`bash scripts/audit.sh` no HEAD `1010999a0b7898bc150692f543bf22af1d12bd25`.
O checker confirmou 70 declarações/50 teoremas; o script terminou em
`kernel audit passed`. `main`/`origin/main` e ancestralidade foram confirmados
antes de iniciar os incrementos dependentes. GitHub Actions permaneceu em
`startup_failure`, sem jobs; `gh run view` indicou possível problema de workflow
sem diagnóstico causal específico. Auditoria no llm não é execução de Actions.
O merge não exigiu bypass/admin/force. O PR #15 Weyl não foi integrado e os pins
permaneceram intactos. Os dois untracked C2OddTfvdTransport permanecem preservados.

## Auditoria dos tipos e das normalizações

| Objeto | Domínio → contradomínio | Índice/normalização/métrica | Resultado existente |
|---|---|---|---|
| `materialJet r` | `FiniteRealSpectralHilbert N` → mesmo Hilbert | posição `a+1`; `log(a+1)^r`; inner conjuga a primeira entrada | `materialJet_apply`, `materialJet_pairing` |
| `relationalWordJetSynthesis` | fibras dependentes de palavras de vozes primas → Hilbert material | repetições e mixed words retidos; ledger independente | `relationalWordJetSynthesis_eq_materialJet` |
| `materialCameraSynthesis` | coeficientes de câmeras → Hilbert de `finiteFamilyWindow` | row literal, todos os crosses; nenhuma amplitude Dirichlet implícita | `materialCameraSynthesis_jet_pairing` |
| `finiteParsevalMaterialEmbedding` | Hilbert material finito → atlas Green/Parseval existente | isometria e domínio logarítmico; índice material permanece | `finiteParsevalMaterialEmbedding_allOrder_step`, `...camera_jet_synthesis` |
| `materialTfvdEnrichedTaylorPrefix N r` | cutoff/ordem → carrier TFVD enriquecido `WithLp 2` | `N` arestas, `N+1` samples; `(-I)^r/r!`; canal log `I*(r+1)` e ordem `r+1` | `materialTfvdEnrichedTaylorPrefix_tendsto` |
| Resposta Green + bordo | câmera suportada/cutoff/ordem/passos → `CarryVerticalL2` | `N=finiteCameraWindow b M+1`; limite em passo para ordem/cutoff fixos | `materialTfvdTaylorPrefix_Green_response_boundary_tendsto` |
| `nativeSourceChiralJetInput n k` (`U`) | `(Fin (2*n) → ℂ)` → mesmo espaço de coeficientes | entrada = ordem radial `a`, saída = nó radial `i`; fase `(-1)^(a/2)`, `1/(a!*h_k^a)`, amplitude completada `A_i` | eventualmente bijetivo em cada dimensão fixa |
| `nativeSourceProjectiveBoundaryJetSynthesis n k` (`J`) | coeficientes de ordem → `CauchyCarrier × CauchyCarrier` | soma de todos os jets even/odd; duas pernas, ambos canais Cauchy originais | `...eq_originalSource` dá `(Incident(Ux),Returned(Ux))` |
| `canonicalCompletedNativeProjectiveChiralForm` | dois pares quirais → ℂ | `1/2*(inner incident - inner returned)`; não produto Hilbert positivo | `...pairing`, `...energy_eq_storage` |
| Energia física quiral | par → ℝ | `Q=2*(norm incident²-norm returned²)=4*Re(form)` | `storage_one_chiralJetInput_eventually_energy_control`; cada dimensão fixa |

Não identificar posição material, ordem de Taylor, profundidade C2, câmera,
cutoff, aresta e passo radial. Nem a igualdade de tipos finitos de coeficientes
nem a igualdade de readouts resolve esse problema geométrico.

Fontes quirais lidas: `CompletedNativeChiralJetStorageTransport`,
`CompletedNativeChiralBoundaryJetTransport`, `CompletedNativeProjectiveChiralCarrier`,
`CompletedNativeProjectiveChiralForwardDifference`; fontes materiais: cinco
módulos do PR #65 e seus carriers importados. A energia de storage inclui
normalizações completadas e a diferença original. O controle eventual é em
dimensão fixa, não uniforme em `n`, cutoff material ou conditioning de `U`.
Além disso, a estimativa fonte usa o norm de `Fin (2*n) → ℂ` (norm Pi),
enquanto o carrier material usa `WithLp 2`; nenhuma estimativa entre esses
norms foi inferida silenciosamente. O novo resultado de energia é uma
igualdade com storage, não uma nova estimativa uniforme material.

## Candidato mínimo auditado, sem novo carrier ou relógio

`MaterialChiralCoordinateCanary.sourceCoordinateInput n k` reutiliza literalmente
`U`, através de `WithLp.toLp 2`, no Hilbert finito existente. O candidato
`sourceCoordinatePair` aplica Incident e Returned ao **mesmo** `Ux`.
A fonte de `U`/dos estados é independente dos jets materiais; nenhum coeficiente
é definido a partir de um Gram desejado. Trata-se de um canário de reutilização
direta de coordenadas, **não** de uma costura física material–fonte já provada.

Antes de qualquer energia, provamos que seu par é a síntese fonte existente e
que ele é injetivo no chart regular: a perna incident é injetiva e `U` é injetivo.
O pairing é expandido em todos os crosses ordenados das duas pernas com
`conj(c_i)*d_j`. A energia continua `2*(norm incident²-norm returned²)` e iguala
o storage original; nenhuma soma positiva a substitui. Não definimos um defeito
entre Grams de fontes incompatíveis, nem uma forma material ajustada para absorvê-lo.

## Ordens zero e um

Se `P_i(k)` é o estado radial projetivo completado e `h_k` o passo original:

```text
projectiveChiralDifferenceJet k 0 = P_0(k)
projectiveChiralDifferenceJet k 1 = h_k⁻¹ • (P_1(k) - P_0(k))
```

`P_0` é o primeiro nó **deslocado**, não a origem. Nenhuma das pernas de `P_i`
é eliminada. Na dimensão 2, escrevendo `A_i` para a amplitude completada:

```text
(Ux)_0 = A_0 * (x_0 - h_k⁻¹*x_1)
(Ux)_1 = A_1 * h_k⁻¹*x_1
Lx = (0, log(2)*x_1)
```

Ordem zero: `U L^0 = L^0 U`, identidade trivial de potência zero; não é
certificação da origem física das coordenadas. Ordem um, no segundo vetor
da base material `e_1`:

```text
((U L - L U)e_1)_0 = -A_0 * h_k⁻¹ * log(2).
```

Esse defeito é não nulo se a característica e a coordenada Hermite–Biehler
forem regulares no primeiro nó, situação eventualmente demonstrada pelo
teorema existente de regularidade radial. `h_k≠0` e `log(2)>0` já são exatos.
Portanto o candidato `U` **não** entrelaça o mesmo relógio material nos dois
lados, já na dimensão 2. Não se trata de uma obstrução universal à costura:
o alvo deve ter uma relação geométrica real entre posição material e ordem
radial, em vez desta identificação direta.

## Defeito arbitrário e perda do seed

Em toda ordem `r`, o comutador foi identificado literalmente:

```text
(U L^r x - L^r Ux)_i =
  sum_a U_(i,a) * (log(a+1)^r - log(i+1)^r) * x_a.
```

Aqui o segundo relógio também é o **mesmo** operador material existente;
esta é a obrigação testada, não a postulação de um operador radial.
Não conjugamos `L` por `U` para fabricar um entrelaçamento. Os fatores `A`,
fases, pesos forward e fatoriais permanecem dentro de `U`.

Outro no-go: no chart regular de dimensão 2, não existe **sequer uma função**
dos slopes finitos para o carrier quiral que reproduza `sourceCoordinatePair`
para todo estado material. O gradiente é não injetivo, enquanto o par completo
é injetivo. Assim, fatorar esse par pelo gradiente sozinho apagaria informação.
O resultado vale eventualmente em `k` sem hipótese de positividade. Ele não
nega um mapa dos slopes **com seed e complementos** e não afirma que qualquer
seed físico tem energia infinita.

## Limite e gate mínimo

O estado nodal crítico permanece sem limite no Green/Parseval isométrico,
pela energia harmônica divergente. Os vetores TFVD de slopes possuem limite
de cada ordem fixa, já provado independentemente. Ainda falta transportar
seed/complementos e as correções completadas junto deles, sem inferir
convergência do vetor nodal bruto. O no-go de fatoração mostra por que apagar
o seed não resolve a costura fiel, mesmo em dimensão 2.

`OPEN_MATERIAL_TO_COMPLETED_CHIRAL_SOURCE_SEWING` permanece aberto, agora com
duas restrições formais: não identificar índices via o chart `U` direto; não
fatorar o par fiel exclusivamente pelo gradiente. O próximo objeto necessário
é um mapa derivado dos dados seed + slopes + complementos para os coeficientes
radiais completados, compatível com as máscaras e as duas sínteses de fonte,
com correções e bordo explícitos. Seus limites/domínios precisam ser provados.

`OPEN_SOURCE_BOUNDARY_POSITIVITY_ALL_ORDER` é independente e não foi fechado.
Não há afirmação de HP, positividade Hankel ou identificação de alturas.

## Validação e publicação

Os resultados e assinaturas finais, comandos, auditoria de todas as declarações
públicas e SHAs são registrados abaixo após a validação no llm. O README recebeu
um índice central com status, módulos, no-gos e gates; os 2001 linhas do
histórico anterior foram conservados abaixo dele.


## Assinaturas dos 15 teoremas novos

Namespace `CarrySelfAdjointOperator.MaterialChiralCanary`. Os teoremas de
injetividade e no-go no chart regular têm regularidade explícita, proveniente
da API da fonte. As versões eventuais derivam a regularidade existente e
não inserem hipótese de positividade. Duas definições públicas usam apenas
os carriers existentes; o helper de polarização é privado.

```lean
theorem sourceCoordinatePair_eq_existingSynthesis (n k : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceCoordinatePair n k x =
      nativeSourceProjectiveBoundaryJetSynthesis n k (fun a => x a)

theorem sourceCoordinatePair_injective (n k : ℕ)
    (hreg : ∀ i : Fin (2*n),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    Function.Injective (sourceCoordinatePair n k)

theorem sourceCoordinatePair_two_not_factor_through_gradient (k : ℕ)
    (hreg : ∀ i : Fin 2,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    ¬ ∃ T : FiniteRealSpectralHilbert 1 → CanonicalCompletedNativeProjectiveChiralCarrier,
      ∀ x : FiniteRealSpectralHilbert 2,
        sourceCoordinatePair 1 k x = T (finiteMaterialGradient 1 x)

theorem sourceCoordinatePair_two_eventually_not_factor_through_gradient :
    ∀ᶠ k : ℕ in atTop,
      ¬ ∃ T : FiniteRealSpectralHilbert 1 → CanonicalCompletedNativeProjectiveChiralCarrier,
        ∀ x : FiniteRealSpectralHilbert 2,
          sourceCoordinatePair 1 k x = T (finiteMaterialGradient 1 x)

theorem sourceCoordinatePair_signed_pairing (n k : ℕ)
    (x y : FiniteRealSpectralHilbert (2*n)) :
    canonicalCompletedNativeProjectiveChiralForm
      (sourceCoordinatePair n k x) (sourceCoordinatePair n k y) =
      (2 : ℂ)⁻¹ *
        (∑ i, ∑ j, conj (sourceCoordinateInput n k x i) *
          sourceCoordinateInput n k y j * inner ℂ
            (completedNativeRadialChiralCauchyState k i)
            (completedNativeRadialChiralCauchyState k j) -
         ∑ i, ∑ j, conj (sourceCoordinateInput n k x i) *
          sourceCoordinateInput n k y j * inner ℂ
            (completedNativeRadialChiralMultiplierState k i)
            (completedNativeRadialChiralMultiplierState k j))

theorem sourceCoordinatePair_energy_eq_storage (n k : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    2 * (‖(sourceCoordinatePair n k x).1‖^2 - ‖(sourceCoordinatePair n k x).2‖^2) =
      2 * (storage k (nativeSourceChiralJetInput n k (fun a => x a)) 1).re

theorem sourceCoordinateInput_materialJet_commutator (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) (i : Fin (2*n)) :
    sourceCoordinateInput n k (materialJet r x) i -
      materialJet r (sourceCoordinateInput n k x) i =
      ∑ a, nativeSourceChiralJetInputMatrix n k i a *
        ((finiteRealSpectralFrequency a : ℂ)^r -
          (finiteRealSpectralFrequency i : ℂ)^r) * x a

theorem sourceCoordinateInput_order_zero (n k : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceCoordinateInput n k (materialJet 0 x) =
      materialJet 0 (sourceCoordinateInput n k x)

theorem projectiveChiralDifferenceJet_zero (k : ℕ) :
    projectiveChiralDifferenceJet k 0 =
      canonicalCompletedNativeRadialProjectiveChiralState k 0

theorem projectiveChiralDifferenceJet_one (k : ℕ) :
    projectiveChiralDifferenceJet k 1 =
      (canonicalCompletedC3RadialSecondStep k)⁻¹ •
        (canonicalCompletedNativeRadialProjectiveChiralState k 1 -
          canonicalCompletedNativeRadialProjectiveChiralState k 0)

theorem sourceCoordinateInput_two_zero (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinateInput 1 k x 0 =
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) *
        (x 0 - (canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1)

theorem sourceCoordinateInput_two_one (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinateInput 1 k x 1 =
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 1) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1

theorem sourceCoordinateInput_two_clock_defect (k : ℕ) :
    sourceCoordinateInput 1 k (materialJet 1 (finiteMaterialBasis (1 : Fin 2))) 0 -
      materialJet 1 (sourceCoordinateInput 1 k (finiteMaterialBasis (1 : Fin 2))) 0 =
      -completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹ * (Real.log 2 : ℂ)

theorem sourceCoordinateInput_two_not_clock_intertwiner (k : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0)
    (hHB : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0) :
    ¬ ∀ x : FiniteRealSpectralHilbert 2,
      sourceCoordinateInput 1 k (materialJet 1 x) =
        materialJet 1 (sourceCoordinateInput 1 k x)

theorem sourceCoordinateInput_two_eventually_not_clock_intertwiner :
    ∀ᶠ k : ℕ in atTop, ¬ ∀ x : FiniteRealSpectralHilbert 2,
      sourceCoordinateInput 1 k (materialJet 1 x) =
        materialJet 1 (sourceCoordinateInput 1 k x)

```

## Estado dos repositórios relacionados (somente leitura)

- `/home/thlinux/native-carry-spectral-weyl`: `871217099a069083791738578b2e44005b31986e`, branch PR #15, clean.
- `/home/thlinux/geometry-of-numbers`: `e1084b43533255b399b82dc307b536d7dfdca07f`, main clean.
- `/home/thlinux/primos`: `8c4b7fdf65a49d1d0febe8193d56e2cfb2191260`, branch ahead 5, alterações CPFormal preexistentes preservadas.

Nenhum deles foi alterado. O repo principal permanece privado. Não criamos
worktrees; os worktrees antigos foram apenas inventariados e preservados.

## Evidências finais de validação no llm

- `lake build --wfail CarrySelfAdjointOperator.MaterialChiralCoordinateCanaryAudit`: passou (9689 jobs), após remover um argumento de simp não usado; nenhum linter foi desabilitado.
- Todas as 17 declarações públicas (15 teoremas, 2 defs) passaram pelo guard `#assert_material_chiral_canary_axioms` e `#print axioms`; somente `propext`, `Classical.choice`, `Quot.sound`.
- `bash scripts/static_audit.sh`: passou; registry material 70/50 e canário 17/15; nenhum trust escape.
- `bash scripts/audit.sh`: passou, incluindo root público, Audit, BR2Audit, OrderAudit, RecoveredC2GreenAudit e todos os audits oficiais; terminou em `kernel audit passed`.
- `git diff --check`: passou. Links relativos do índice README verificados; texto histórico anterior preservado integralmente.
- Não houve experimentos numéricos nesta etapa; o defeito e os no-gos são exatos e kernel-checked.

Logs no llm: `/tmp/pr65-integration-audit.log`, `/tmp/material-chiral-canary-axioms.log`, `/tmp/material-chiral-full-audit.log`. Cópias integrais acompanham a entrega. Publicação e sincronização final registradas no checkpoint de entrega.

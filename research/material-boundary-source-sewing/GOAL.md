# Mano — Costura física real e relacional da positividade Carry

**Repositório principal:** `thiagomassensini/carry-self-adjoint-operator`.

**Objetivo:** investigar e, quando possível, formalizar em Lean 4 uma ponte física independente entre a geometria nativa multibase, sua energia positiva e a fonte quiral completada, sem construir outra Gram positiva e sem recorrer aos certificados theta como premissas.

## Princípio obrigatório

**Não escalarizar antes da síntese completa.**

Conservar os estados físicos, as duas quadraturas reais, os índices materiais, câmeras, centros, pernas, profundidades, relógio logarítmico, bordos, caudas, retornos e todos os produtos cruzados até finalizar o transporte vetorial e bilinear.

A câmera é uma representação da geometria dos inteiros, não uma liberdade para escolher outra energia.

## Inventário obrigatório

Inspecionar os teoremas já existentes:

- Em `native-carry-spectral-weyl`: `finiteGramMatrix_quadratic_eq_sum_sq`, `finiteGramMatrix_posDef`, `gramForm_pos` e `cameraEmbedding_inner`. Conferir separadamente o PR #15, ainda não integrado na auditoria, com a realização por `1/lcm(d,e)` e a obstrução da segunda diferença no span periódico.
- Em `green-frame-theorem`: `carryCameraWeight_finsum_eq_one`, `concreteAnalysisOperator_norm_sq_bounds`, `frameOperator_strictlyPositive` e os operadores originais de Green, semente e residual.
- Em `geometry-of-numbers`: `c2GlobalRestrictedGreenGram_strictlyPositive`, `completeVerticalObservabilityGram_posDef` e os no-gos que impedem identificar uma incidência isométrica nua com a Hankel canônica.
- Em `carry-self-adjoint-operator`: `materialCameraSynthesis_jet_pairing`, `materialCameraPairing_zero_eq_periodicGram_add_residue`, `cameraMaterialJet_eq_seed_add_radiusSum`, `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource`, `nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage`, `NaimarkProjectorIntertwiningSeam` e `canonicalCompletedNativeGreenMomentGramDefect`.

Reutilizar as provas sem alterar os objetos originais.

## Etapa principal

Construir ou delimitar um mapa tipado que parta dos estados e estênceis materiais verdadeiros, com os respectivos coeficientes, e alcance as entradas do par quiral completado.

O transporte precisa distinguir rigorosamente posição material, profundidade, label da câmera, ordem de derivada temporal, grau radial, cutoff e passo radial.

Primeiro demonstrar identidades de vetores inteiros. Depois, para dois inputs independentes, transportar todos os pareamentos, preservando inclusive GG/GR/RG/RR, o canal antipodal das câmeras pares e o residual analítico.

Comparar com a **forma assinada original** incidente menos retorno, sem trocar a métrica e sem presumir seu sinal.

Se a identidade falhar, derivar o defeito exato a partir dos operadores originais, localizar sua primeira contribuição não nula e fornecer uma testemunha formal. Não basta definir o defeito como diferença entre dois resultados e provar uma equivalência tautológica.

## Primeira entrega viável

Preferir um incremento matemático pequeno e genuíno: uma costura source-correct de dimensão 2 ou 4 que avance além dos resultados já formalizados da primeira aresta; ou uma identidade universal dos bordos físicos no mesmo carrier material, com todos os cruzamentos; ou o primeiro quadrado concreto de entrelaçamento dos projetores finito/Naimark.

Não tentar provar simultaneamente toda a positividade all-order. A identidade física deve vir primeiro.

## Regras de segurança matemática

Não usar Cholesky, whitening, momentos theta, zeros, alturas ou Jacobi para definir a fonte ou fabricar positividade.

Não identificar automaticamente a Gram periódica multibase, a Gram rotante do operador primitivo, a Gram TFVD e a energia quiral assinada.

Não eliminar resíduos de cutoff, caudas, termos de retorno, correções antipodais, cruzamentos mistos ou defeitos de comutador.

Não postular `PosDef`, HP, Herglotz ou uma representação positiva que já contenha a conclusão.

Não presumir coercividade uniforme nas coordenadas brutas dos momentos: existem obstruções formalizadas.

## Entregas e validação

Produzir módulos Lean compiláveis com provas não circulares, registros de axiomas, `lake build --wfail`, regressões dos casos C2, C3, C4, C5, e relatório humano.

Classificar cada resultado como **PASS**, **CONDICIONAL**, **OPEN** ou **NO-GO**, com o enunciado exato que justifica a classificação.

Preservar pins e trabalho local, abrir PR descritivo sem merge automático.

**Critério de sucesso:** uma identidade física nova e auditável entre as estruturas originais, ou um defeito/no-go exato que localize por que a costura ainda não fecha. Não substituir o problema por outro Gram positivo.
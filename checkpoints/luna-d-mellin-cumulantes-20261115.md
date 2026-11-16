# Checkpoint D — fonte Mellin e cumulantes

Data: 15/11/2026. Estado: parcial, com módulos Lean compilados e auditados; a identificação Mellin infinita e a ponte analítica aos cumulantes ainda estão abertas.

## Base e proveniência

- A branch é baseada no commit `87e448a6c2fdd35b61cc3f6ff824bef9dc1b4b88`, cabeça da PR draft #117, empilhada sobre a contribuição de pernas da #116. A PR #117 e a #116 permaneciam abertas quando esta tarefa começou; as declarações de pernas polarizadas da #112 já estavam integradas em `main`.
- O checkout principal estava sujo. Foi preservado sem alterações; o trabalho ocorreu em worktree separada.
- Não havia `AGENTS.md` na raiz do CSA nem em seus diretórios de código alterados. Li o `AGENTS.md` do pacote dependente `geometry-of-numbers`; as regras pertinentes de proveniência e de não introduzir axiomas foram respeitadas. A regra de não fazer commit/push sem pedido está satisfeita pela autorização explícita desta tarefa.

## O que ficou formalizado

1. `C2MellinPositiveDensity.lean` define a densidade original `w(x)=exp(-x)+omega0(x)`, sua forma racional em `q=exp(-x)`, as densidades da cabeça e da cauda e o integral Mellin real.
   - Prova a identidade `omega0 = exp(-4x) · 4 sinh²(x/2)/(1-exp(-4x))` para `x>0`.
   - Prova `omega0>0`, `0<w≤2exp(-x)`, positividade da cabeça e não negatividade da cauda.
   - Prova exatamente `w_H,M+w_T,M=w` para todo `M`.
   - Registra o alias da carta C2 original como `bracketCharacteristic 2`; não redefine a carta por um integral.
   - Prova a transformada Mellin de um único termo exponencial usando `Real.integral_rpow_mul_exp_neg_mul_Ioi`.
   - Declara as obrigações `nativeC2MellinHeadGammaIdentificationObligation`, `nativeC2MellinTailGammaIdentificationObligation`, `nativeC2MellinGammaIdentificationObligation` e `nativeC2MellinIteratedDerivativeObligation`, sem axiomatizá-las.
2. `C2MellinFormalCumulants.lean` define o núcleo formal de cumulantes por recursão forte e prova a recorrência na forma `Fin n` e na forma equivalente de soma em `range n`.
3. `C2MellinMixtureIdentities.lean` prova algebricamente:
   - `Xi = p (mu_H-mu_T)` na expressão original com `V_M`, `T_M`, `J_M` e `J_T`;
   - cancelamento do termo comum de `Gamma'/Gamma`;
   - decomposição da variância da mistura e a identidade da diferença para a variância da cabeça, conservando `p(VarT-VarH)`;
   - não negatividade do termo entre médias quando `0≤p≤1`.
4. `C2MellinCumulantsAudit.lean` audita estes resultados e as declarações originais de momento Wronskiano e dressing archimediano.

## Declarações originais conferidas

- `C2GeometryNativeSourceBridge.lean`: a fonte continua sendo seed mais brackets, e o teorema de cabeça + cauda usa a carta nativa original.
- `CompletedNativeC2ExactTailTransport.lean`: `nativeC2ExactCenterTail`, igualdade da cauda com carta completa menos cabeça e transporte do companion com derivada da câmera/Gamma foram conferidos.
- `C2LegCompletionPolarization.lean`: o companion completado e o Wronskiano mantêm os cruzamentos das pernas.
- `CompletedNativeTfvdWronskianMoments.lean`: os momentos canônicos continuam definidos pelo readout Wronskiano original.
- `NativeBoundaryArchimedeanDressingSeparation.lean`: `completedNativeLogDerivative_eq_native_add_archimedean` conserva a contribuição do fator de completamento; o mismatch Gamma–Wronskiano continua explícito.

## Obrigações exatas ainda abertas

1. **Identificação Mellin da cabeça e da cauda:** provar a soma geométrica dos kernels de célula, a transformada termo a termo em `dirichletValue`/`centerBracketTerm` da câmera 2 e a troca integral–série (Tonelli ou convergência dominada). Isso prova as três proposições de identificação declaradas. A infraestrutura de Euler para cada taxa exponencial está disponível e formalizada; a troca para a série geométrica infinita não está.
2. **Derivadas da fonte:** formalizar integrabilidade local dos majorantes e diferenciação sob o integral para cada ordem. A obrigação aponta para `iteratedDeriv` do integral fonte e o momento de `log x`; ainda não prova os limites do pacote `2 x^(a-1)|log x|^r` e `2 x^(b+r-1)e^-x` nem suas integrais.
3. **Cumulantes analíticos:** ligar os momentos normalizados ao cumulante formal e provar a obrigação de derivadas de `log Z`. A recorrência formal sozinha não fornece essa identificação.
4. **Dressing e readout:** derivar a positividade de `D(s)` na faixa `0<s<1` pela fórmula original e duplicação de Gamma, então provar a conversão do coeficiente na variável `s=1/2+iz` para o momento canônico, incluindo os fatores `i` e `2`. A auditoria registra a separação original de dressing, mas esta nova conversão de ordem arbitrária ainda não foi provada.
5. **Mistura:** as identidades em `V,T,J_M,J_T` estão provadas; falta identificá-las analiticamente com as médias e variâncias dos integrais definidos. Nenhum sinal universal de `Xi` foi assumido. O reprodutor mostra a mudança de sinal entre `M=1` e `M=2` em `s=1/2`.

Não foi afirmada positividade all-order da sequência de momentos de alturas, nem usado zeta/zeros como definição ou insumo.

## Validação

- Os quatro módulos Lean foram verificados com `lake env lean -DwarningAsError=true` e outputs `.olean` na worktree.
- A auditoria `#print axioms` mostrou apenas `[propext, Classical.choice, Quot.sound]` nas novas provas e nas declarações originais amostradas; não há `sorry`, `admit` ou axiomas novos nos arquivos desta branch.
- `investigar_mellin_cumulantes.py` foi executado. `resultados_mellin_cumulantes.json` continuou com SHA-256 `33a9860b72f16f1021be913501da98099559b8f27de68dc3fcce3ac7d10c7800`; permanece experimento multiprecisão (65/90 dps), não certificado intervalar.

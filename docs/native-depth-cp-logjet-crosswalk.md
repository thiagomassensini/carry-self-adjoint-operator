# Comutador de profundidade e coeficiente radial Cp

## Resultado

Base desta rodada: `d85194083013eccf60ec73f3a4cd1c617a28712a`, que contém
o intertwining Newton–Stirling e o comutador discreto. A `main` remota
conferida no início estava em `ac883d23cb94bea793108455054f43d1d0c89387`.
Branch: `agent/native-depth-cp-logjet-crosswalk`.

O novo módulo `NativeDepthCpLogJetCommutatorCrosswalk.lean` prova a ponte
entre o comutador covariante na torre e o coeficiente do comutador Cp
horizontal. Os vetores de origem permanecem distintos.

Usamos literalmente o monômio existente:

\[
\psi_{p,s}(k)=\texttt{natDirichletTerm}\ s\ (p^k),
\qquad q_p=\texttt{primeCarryAmplitudeRatio}\ p.
\]

Com os operadores existentes, em `Module.End ℂ (ℕ → ℂ)`, definimos na
notação deste documento

\[
C_p=[\nabla_{q_p},L_p],\qquad L_pf(k)=\log(p^k)f(k).
\]

O teorema principal, no namespace `CarrySelfAdjointOperator.ProjectiveDepth`, é:

`phaseNormalizedCpLogJetCommutator_eq_depthOperatorReadout`

Para todo `p ≠ 0`, `s : ℂ` e `n : ℕ`, ele prova

\[
\boxed{
\texttt{phaseNormalizedCpLogJetCommutator}(p,s,n)
=\left[p^{i\operatorname{Im}s}(C_p\psi_{p,s})(0)\right]
\texttt{positiveDirichletGradient}(s,n).
}
\]

A leitura em zero é justificada por `nativeDirichletTower_zero`: a semente
vale exatamente 1. Não se divide pelo vetor, pelo gradiente ou por uma
característica. O índice vertical `k` e o índice horizontal `n` não foram
identificados.

## Normalização: o fator crítico entra uma única vez

`cpPhaseNormalizer p s` já remove fase **e** amplitude crítica:

\[
\texttt{cpPhaseNormalizer}(p,s)=p^{1/2+i\operatorname{Im}s}.
\]

A conexão vertical já inclui `q_p⁻¹`. Por isso o normalizador vertical
correto remove só a fase:

\[
\texttt{nativeDepthPhaseNormalizer}(p,s)=p^{i\operatorname{Im}s}.
\]

`nativeDepthPhaseNormalizer_mul_ratio_inv` prova, para `p ≠ 0`,

\[
p^{i\operatorname{Im}s}q_p^{-1}
=\texttt{cpPhaseNormalizer}(p,s).
\]

Não há constante ajustada nem segunda aplicação da escala crítica.

## Cadeia formal

1. `nativeDirichletTower_succ` reutiliza `natDirichletTerm_mul`:
   \(\psi(k+1)=p^{-s}\psi(k)\).
2. `nativeDepthShift_nativeDirichletTower` prova
   \((\nabla_{q_p}+I)\psi=(q_p^{-1}p^{-s})\psi\).
   `nativeDepthShiftEigenvalue_eq_cpow` identifica esse fator com
   \(p^{1/2-s}\), para `p ≠ 0`.
3. `nativeDepthCommutator_nativeDirichletTower` aplica o teorema já existente
   `nativeDepthDifference_logMultiplication_commutator` à mesma torre.
4. `normalizedDepthCommutatorEigenvalue_eq_cpLogScale` prova
   \(\lambda_{\rm depth}^{\rm norm}
   =\texttt{cpPhaseNormalizer}\cdot\texttt{cpLogScaleCoefficient}\).
5. `phaseNormalizedCpLogJetCommutator_eq_depthEigenvalue_mul_gradient`
   reutiliza `cpLogJetCommutator_eq_logScale_mul_gradient`, com `p ≠ 0`.
6. Para `Nat.Prime p`,
   `normalizedDepthCommutatorEigenvalue_eq_radial_logScale` reutiliza
   `cpPhaseNormalizer_mul_eigenvalue` e entrega

   \[
   \lambda_{\rm depth}^{\rm norm}
   =(\log p)p^{-\delta},\qquad
   \delta=\texttt{criticalDisplacement}(\operatorname{Re}s).
   \]

7. `normalizedDepthCommutator_at_zero` e o teorema principal substituem o
   nome do autovalor pela leitura do operador concreto na semente.
8. `canonicalCpLogJetCommutatorSeries_normalized_eq_depthEigenvalue`
   transporta a igualdade coeficiente a coeficiente às séries já definidas
   em `CompletedC3ValveNaturality.lean`.
9. `toProjective_normalizedCpLogJetCommutatorSeries_eq_depthEigenvalue`
   aplica o `toProjective` existente à mesma igualdade de séries completas.

O resultado radial reaproveita a hipótese de primalidade da API existente;
a ponte operador–Cp em si só exige base não nula. Nenhuma hipótese espectral
nova foi usada. Todas as identidades são algébricas ou identidades de
potências; não se afirma que todo `s` fornece um vetor em ℓ².

## Fronteira exata desta rodada

Foi identificado o coeficiente operador/escalar que multiplica o gradiente
horizontal. Não foi construída uma isometria entre esse gradiente e a
torre, nem identificada a métrica nativa dos momentos.

`FiniteEnrichedCameraState.lean` já fornece
`NativeCarryC3Crosswalk.finiteCanonicalEnrichedCamera_reconstruct`.
O enunciado inspecionado exige uma matriz de câmera **real**, com
`(finiteCameraRowGram C).PosDef`, e recebe uma matriz real quadrada `J`.
O próximo passo precisará definir o cutoff do operador e provar sua
compatibilidade com essa câmera. A identidade de reconstrução isolada não
identifica seu canal visível com Cp. O canal cego deverá ser preservado.

`C3ProjectiveHilbertRBBridge.lean` fornece recovery do estado vertical e
portos finitos; isso não torna automaticamente o comutador da presente
torre um endomorfismo limitado daquele Hilbert.

O refinamento de stencils fica para depois dessa identificação finita,
conforme a ordem da proposta. Não há aqui conclusão de positividade do
kernel nativo, sewing Gamma–Wronskiano, certificado HP ou curvatura de Cartan.

## Arquivos

- `CarrySelfAdjointOperator/NativeDepthCpLogJetCommutatorCrosswalk.lean`
- `CarrySelfAdjointOperator/NativeDepthCpLogJetCommutatorCrosswalkAudit.lean`
- Imports nos aggregators `CarrySelfAdjointOperator.lean`, `Audit.lean` e
  `KernelConstructionAudit.lean`.
- Quatorze declarações registradas em `audit/theorem-registry.json`.

Os pins, mathlib e toolchain foram preservados. Os arquivos não rastreados
preexistentes no workspace não fazem parte desta alteração.

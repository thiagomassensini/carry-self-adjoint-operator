# A diferença de profundidade nos frames de potência e Newton

Base desta rodada: `ac883d23cb94bea793108455054f43d1d0c89387`, com o transporte
de Stirling já integrado. A implementação reutiliza `NewtonStirlingTransport`
e `NewtonCarryGreenBridge`; os pins de dependência são preservados.

## Quatro resultados

No módulo
[NewtonStirlingOperatorIntertwining.lean](../CarrySelfAdjointOperator/NewtonStirlingOperatorIntertwining.lean),
o namespace é `CarrySelfAdjointOperator.ProjectiveDepth`.

1. `carryWeightedScalarFirstDifference_powerDepthJet`, para `q ≠ 0`:

   $$
   P_r^{(q)}(k)=k^r q^k,
   \qquad
   \nabla_qP_r^{(q)}=
   \sum_{m<r}\binom rm P_m^{(q)}.
   $$

   A diferença é a definição existente
   `CPFormal.Analytic.Cp.carryWeightedScalarFirstDifference`. Em `r=0`, a
   soma é vazia e o resultado é zero.

2. `powerDifferenceMatrix_mul_stirlingNewtonMatrix`, para todo `N : ℕ`:

   $$
   \boxed{\Delta_{\rm power}^{(N)}S_N=S_NJ_{\rm Newton}^{(N)}}.
   $$

   `powerDifferenceMatrix_eq_stirling_conjugate` também fornece

   $$
   \Delta_{\rm power}^{(N)}=S_NJ_{\rm Newton}^{(N)}S_N^{-1}.
   $$

3. `weightedDepthDifference_depthMultiplication_commutator`, para todo `q : ℂ`:

   $$
   Kf(k)=kf(k),
   \qquad
   \boxed{[\nabla_q,K]=\nabla_q+I}.
   $$

   O enunciado é uma igualdade em `Module.End ℂ (ℕ → ℂ)`.
   `weightedDepthDifferenceLinear` apenas empacota linearmente a diferença
   existente. A identidade de comutador não precisa de `q ≠ 0`; essa condição
   entra na identificação da ação sobre os jets vestidos.

4. `nativeDepthDifference_logMultiplication_commutator`:

   $$
   L_p=(\log p)K,
   \qquad
   \boxed{[\nabla_{q_p},L_p]=(\log p)(\nabla_{q_p}+I)}.
   $$

   `q_p` é o `primeCarryAmplitudeRatio` existente.
   `towerLogMultiplication_apply` verifica literalmente
   `L_p f(k) = log(p^k) f(k)`, pela identidade `Real.log_pow`.

## Convenção matricial e prova da conjugação

O `stirlingNewtonMatrix N` existente tem

$$
(S_N)_{ij}=S(i,j)j!,
\qquad
\mathbf P(k)=S_N\mathbf E(k).
$$

As colunas `P(k)` e `E(k)` listam **amostras dos elementos do frame**,
na ordem `0,…,N`. As linhas das matrizes de diferença descrevem as imagens
desses elementos:

$$
(\Delta_{\rm power})_{ij}=
\begin{cases}\binom ij&j<i,\\0&\text{caso contrário},\end{cases}
\qquad
(J_{\rm Newton})_{ij}=
\begin{cases}1&i=j+1,\\0&\text{caso contrário}.\end{cases}
$$

`powerDifferenceMatrix_mulVec_powerDepthJet` e
`newtonDifferenceMatrix_mulVec_newtonJet` provam essas ações nas sequências
concretas. `carryWeightedScalarFirstDifference_mulVec` prova que a diferença
comuta com qualquer leitura matricial constante finita.

A comparação resulta em `(ΔS)E(k)=(SJ)E(k)`. Para obter igualdade de matrizes,
a prova usa a matriz finita de avaliação `V_{jk}=choose(k,j)` em `0,…,N`:
ela é triangular com diagonal um, portanto tem determinante um e pode ser
cancelada. Esse passo algébrico usa `q=1` apenas como avaliação de polinômios;
não altera a amplitude nativa nem presume que essa amostra esteja em `ℓ²`.

O inverso de `S_N` é justificado pelo teorema já existente
`stirlingNewtonMatrix_det_ne_zero`. A identidade inclui `N=0`.

Para uma **coluna de coeficientes** de combinação de elementos do frame,
as matrizes de ação correspondentes são as transpostas. A orientação acima
acompanha a convenção do módulo anterior.

## Reutilização e fronteira

Cadeia usada: `pow_mul_amplitude_eq_sum_newtonJet` →
`stirlingNewtonMatrix_mulVec_newtonJet`, junto com
`carryWeightedScalarFirstDifference_newtonJet_zero/succ` → ações matriciais →
intertwining → conjugação pelo inverso já disponível.

O operador `K` atua sobre o espaço algébrico completo de sequências. Ele não
preserva o prefixo de grau `N`: `K P_N=P_{N+1}`. Não há truncagem silenciosa de
`K`, nem afirmação de que esses operadores sejam limitados em todo `ℓ²`.

O comutador horizontal `cpLogJetCommutator` continua sendo outro objeto:
ele compara a soma de um bloco de câmera com a ação de seu autovalor no
gradiente logarítmico. O fator `log p` aparece em ambos, mas a igualdade entre
essas realizações exige um mapa adicional demonstrado. Este módulo fornece
a relação vertical exata para essa comparação futura.

Nenhuma isometria, forma de Gram nativa, identificação com o shift espectral
Green, fechamento de operador ou conclusão espectral é pressuposta ou
deduzida. O defeito conhecido da métrica C3 literal continua pertinente à
etapa métrica; não é usado como hipótese destas identidades algébricas.

## Auditoria

[NewtonStirlingOperatorIntertwiningAudit.lean](../CarrySelfAdjointOperator/NewtonStirlingOperatorIntertwiningAudit.lean)
imprime os axiomas dos doze resultados públicos. A implementação e seu audit
estão integrados aos agregadores e ao registro de teoremas do projeto.

Validação executada: o build focado com `--wfail` do audit novo passou;
os doze resultados dependem apenas de `propext`, `Classical.choice` e `Quot.sound`.
`scripts/audit.sh` completou os 15 builds, incluindo o agregador principal e
os audits globais, com `kernel audit passed` e código de saída zero.
A auditoria estática e `git diff --check` passaram. Não houve alteração no
`lean-toolchain`, `lakefile.toml` ou `lake-manifest.json`.

# API existente: massa atômica, ordem e fonte cíclica

> Relatório de uma subinvestigação. Consulte o [estado consolidado da entrega](../README.md) para a integração dos dois novos módulos Lean, a auditoria final e a obrigação que continua aberta.

Auditoria somente de leitura, 2026-09-04, servidor `llm`, repositório `~/carry-self-adjoint-operator`, HEAD `b01bf33f5ab78a02ebb8e48e74af2048b58e1637`.

**Conclusão:** `CompletedNativeJacobiCyclicAtomicExtraction.lean` já constrói a massa positiva e extrai o autovetor através de um limite de vetores resolventes. Ainda não expressa essa massa como `N/z₀²`, onde `N=analyticOrderNatAt F z₀`. O novo lema local que identifica o coeficiente do polo com a ordem é um complemento necessário, sem duplicar o mecanismo de extração atômica.

## Declarações existentes

Todos os nomes abaixo pertencem a `CarrySelfAdjointOperator`; os do arquivo de extração, ao namespace adicional `CompletedNativeRealHPCarrierCertificate`.

| Peça | Arquivo e linha | Conteúdo efetivo |
|---|---|---|
| `completedNativeOperatorLogDerivative` | `CompletedNativeLogDerivativePoles.lean:26` | `−deriv F z / F z`, sem fator `1/2` |
| `completedNativeOperatorCharacteristic_analyticOrderAt_ne_top` | Mesmo arquivo:43 | Ordem analítica finita na faixa natural |
| `completedNativeOperatorCharacteristic_analyticOrderNatAt_ne_zero` | Mesmo arquivo:52 | Multiplicidade natural positiva nos zeros |
| `completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one` | Mesmo arquivo:69 | Ordem meromórfica `−1`; usa `N` mas não calcula o coeficiente líder |
| `completedNativeJacobiWeylHeightContinuation` | `CompletedNativeJacobiWeylContinuation.lean:28` | Fora de zero, `(-F′/F)/(2z)` |
| `..._meromorphicOrderAt_eq_neg_one_iff_zero` | Mesmo arquivo:115 | Polo simples da função Weyl equivale a zero nativo |
| `positiveJacobiAtomicCyclicResidue` | `CompletedNativeJacobiCyclicAtomicExtraction.lean:418` | `(2/z₀) * meromorphicTrailingCoeffAt WeylHeight z₀` |
| `positiveJacobiAtomicCyclicScaledReadout_eq_weyl` | Mesmo arquivo:425 | Conversão exata pela coordenada `λ=z⁻²` |
| `positiveJacobiAtomicCyclicScaledReadout_tendsto` | Mesmo arquivo:482 | Limite escalar igual ao resíduo cíclico definido |
| `positiveJacobiAtomicCyclicResidue_conj` | Mesmo arquivo:806 | Resíduo real sob certificado e zero real |
| `positiveJacobiAtomicCyclicResidue_ne_zero` | Mesmo arquivo:834 | Resíduo não nulo, sem usar uma fórmula em `N` |
| `positiveJacobiAtomicCyclicMass` | Mesmo arquivo:868 | `−(positiveJacobiAtomicCyclicResidue z₀).re` |
| `positiveJacobiAtomicCyclicMass_pos` | Mesmo arquivo:902 | Massa estritamente positiva sob certificado |
| `inner_positiveJacobiAtomicCyclicScaledVector_tendsto` | Mesmo arquivo:1124 | Todos os produtos cruzados dos vetores escalados tendem à massa |
| `exists_positiveJacobiAtomicCyclicVector` | Mesmo arquivo:1172 | Limite vetorial não nulo, sem medida espectral pressuposta |

O arquivo termina transportando o autovalor `λ₀=z₀⁻²` para o operador de altura. Não assume uma decomposição puramente pontual global.

## Sinal e fator exatos

Se o novo lema provar, para `N=analyticOrderNatAt F z₀`,

$$
\operatorname{trailing}_{z_0}(-F'/F)=-N,
$$

então a normalização existente exige

$$
\operatorname{trailing}_{z_0}(W)=-\frac{N}{2z_0},\qquad
\operatorname{residue}_{\mathrm{cyclic}}=-\frac{N}{z_0^2}.
$$

Para zero real não nulo,

$$
m_{\mathrm{atom}}=\frac{N}{(\Re z_0)^2}=N\lambda_0,
\qquad \lambda_0=z_0^{-2}.
$$

Essa cadeia é uma dedução algébrica conferida contra as definições; a igualdade final ainda não consta como declaração no módulo auditado. O parâmetro cíclico usa a convenção `(J−λ)⁻¹`, cujo resíduo em `λ=λ₀` é a massa com sinal negativo.

O estado-limite possui norma quadrática igual à massa. O argumento já aparece internamente no lema genérico `CyclicAtomicExtraction.exists_ne_zero_tendsto_of_inner_tendsto`, linhas 27–90: a unicidade do limite de normas produz `mass = ‖v‖²` na linha 86, mas a conclusão pública do lema retém apenas `v≠0` e a convergência. Expor a igualdade da norma é um corolário de continuidade, sem nova construção.

## Fonte: o que já existe e o que não está identificado geometricamente

`positiveJacobiCyclicHead`, em `CompletedNativePositiveJacobiResolvent.lean:616`, é exatamente

```lean
ComplexifiedOrbitResolvent.ofReal (completedJacobiOrbit jet 0)
```

`greenJetJacobiCoreCyclicMoment_eq` (`CompletedNativeJacobiCyclicReadout.lean:97`) e as especializações `..._eq_canonicalLogDerivativeMoment` identificam os momentos dessa cabeça **sob o certificado de representação Gram**. A cabeça não é definida nesses módulos por uma fórmula aritmética `√peso/clock`.

`completedJacobiEigenvector_cyclicHead_ne_zero` (`CompletedNativeJacobiPointSpectrumConverse.lean:203`) assegura que todo autovetor pontual é visto pela cabeça. Na prova seguinte, linhas 243–256, a identidade do produto interno com o vetor resolvente escalado é explícita. Ela mantém a interpretação de massa como energia da projeção cíclica; não a identifica com uma sequência carry independente do certificado.

Se se escolhesse uma base atômica ortonormal com altura positiva `z₀`, a fórmula `m=N/z₀²` permitiria a amplitude `√N/z₀`. Essa é uma interpretação **após** a identificação espectral; o módulo não constrói essa fonte geométrica a partir de profundidades/arredondamentos carry.

## Consequência para os dois candidatos diagonais

No modelo

$$
a(t)=t\sum_j\frac{m_j}{1-t^2\lambda_j},
$$

o resíduo no polo de altura `z_j=λ_j⁻¹ᐟ²` é `−m_j/(2λ_j)`. Para coincidir com `−F′/(2F)`, o quociente `m_j/λ_j` deve ser a multiplicidade inteira positiva, se o polo está na faixa e não há outra contribuição cancelando/modificando esse mesmo átomo.

- Candidato anterior: `λ_n=1/log²n`, `m_n=1/(n log²n)`. O quociente é `1/n`; isso explica a incompatibilidade de resíduo desse modelo específico.
- Novo candidato proposto pelo agente principal: `λ_n=m_n=1/(n log²n)`, `u_n=√m_n`, `S_n=√λ_n`. O quociente é `1`, compatível com zeros simples. Isso corrige a multiplicidade dos polos do candidato, mas não identifica sua função com a característica nativa; a comparação de momentos continua necessária.

O valor já calculado de `∑m_n` foi enviado ao agente responsável pelo novo teste, com o JSON e o controle de Euler–Maclaurin. Não se repetiu a soma.

## Mathlib e evidência de fonte

Não foi localizada, no diretório `Mathlib/Analysis/Meromorphic` consumido por este checkout, uma declaração nomeada que calcule diretamente o coeficiente líder da derivada ou da log derivada em termos da ordem. `MeromorphicAt.meromorphicTrailingCoeffAt_mul` existe em `TrailingCoefficient.lean:395`; a variante de produto por escalar, em 363. A fórmula local por fatoração da ordem que o outro agente está implementando não duplica uma declaração nativa encontrada nesta busca.

| Arquivo | SHA256 |
|---|---|
| `CompletedNativeJacobiCyclicAtomicExtraction.lean` | `00ba2a784c79c34157dda9c69f964754bef963e37b8ca20703c64b7b96670fdd` |
| `CompletedNativeLogDerivativePoles.lean` | `b5fb4056f235f168d9ded90a12299cdadef4b85ede19073882e22a8ac8ac4a44` |
| `CompletedNativeJacobiWeylContinuation.lean` | `1e385930053ed1340e586ddcf96b2a2a2aff948e7866511a0de085dfae7e3fc3` |
| `CompletedNativeJacobiCyclicReadout.lean` | `672091addecf4be27b6a6a2c46b284eedc2e75cfa8c0dac2d14fb7f0cb1aa551` |
| `CompletedNativeJacobiCyclicStieltjesReadout.lean` | `b0d08ee2f79fcfac400cee41f7f0a68dd6a22a09a0928e82d03c1e9925bb21f6` |

Nenhuma fonte Lean ou estado Git foi alterado nesta auditoria.

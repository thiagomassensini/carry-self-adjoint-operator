# Garimpo das notas: retorno, sondas e Green em duas variáveis

> **Atualização após a tentativa de construção do kernel (04/09/2026).** O kernel de resolvente positivo, sua diagonal, séries e Grams foram formalizados. A costura do estado C3 concreto com a métrica ortogonal padrão foi **refutada no Lean**: seu Gram central excede o momento nativo. A igualdade dessa realização específica deixou de ser uma meta aberta. A rota com outra métrica/observável permanece em investigação. Veja [a construção e a obrigação atual](../construcao-kernel-carry.md), commit `7c778e4`. O conteúdo abaixo registra o estado anterior desse mapeamento.

Auditoria de fontes em 2026-09-04. Notas originais preservadas. `Lean` abaixo significa declaração/prova localizada no snapshot indicado; não foi executado um novo build nesta auditoria. `Derivação` identifica álgebra conferida neste trabalho, ainda sem novo lema Lean. As palavras “fechado” das notas não foram usadas como prova automática nem as palavras “STOP” como proibição geral.

## Resultado que muda a próxima etapa

A métrica de retorno é uma peça **já formalizada** no Weyl, inclusive na dependência consumida pelo autoadjunto. As notas fornecem a apresentação do mecanismo: preservação exata do estado endpoint+bulk e inserção de observáveis. A versão polarizada com dois resolventes é uma consequência algébrica curta dessa mesma identidade. Não é necessário reconstruir esse fundamento.

O alvo específico ainda não identificado nestas notas é o **readout escalar e o parâmetro** que tornam esse resolvente a resposta nativa `a = −F′/(2F)`, ou que identificam sua forma com o Gram do estado concreto SA3. As variantes ampliadas dos registros de sondas reconhecem justamente o alvo `G_N=X_N*X_N`, `K_N=X_N*Y_carry X_N` e não fornecem a igualdade com os momentos nativos. Isso é um resultado da leitura, não um veto a procurar a igualdade em outra nota.

Também há uma correção documental importante: a fórmula correta da geradora **já aparece na nota analítica detalhada**, embora o resumo dos registros a tenha copiado incorretamente.

## 1. Notas prioritárias e localização

| Nota | Trecho | Peça concreta | Situação após confronto atual |
|---|---|---|---|
| [native_carry_registro_pesquisa_sondas_defeito_pt.md](</home/thlinux/Downloads/native_carry_registro_pesquisa_sondas_defeito_pt.md>) | 150–247 | Sonda `S=C R E*`, métrica `G_E=I+P*P`, cancelamento `E*G_E E=I`, limite da covariância normalizada | Cancelamento e covariância formalizados; ver seção 3. |
| [UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md](</home/thlinux/Downloads/UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md>) | 149–188, 191–270 | Deriva a métrica da isometria `V=(E,B)` e explica por que a métrica dual produz `S G_E S*` | Excelente fonte para tipar o lema: `P E=B`, `E*E+B*B=I`; nenhuma hipótese espectral necessária para o cancelamento. |
| [UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md](</home/thlinux/Downloads/UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md>) | 274–354, 507–543 | Limite periódico em norma, para pacote finito fixo de câmeras e âncora não real fixa | O limite direto já existe em Lean; instanciar a família de coligações e conferir dimensões, abaixo. |
| [CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md](</home/thlinux/Downloads/CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md>) | 47–129, 188–229, 272–348 | Observable `p(L−μ)` dentro da sonda; medida `D(x) M_0 D(x) dx`; argumento analítico de convergência | Álgebra funcional de grau arbitrário formalizada; limite analítico no snapshot explicitamente concluído até grau oito. |
| [CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md](</home/thlinux/Downloads/CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md>) | 388–434, especialmente 411–422 | Geradora correta `m_0 e^s ℓ^(s+1)/(1+s)` | Corrige o resumo dos registros sem inventar fórmula nova. |
| [TRANSFORMADA_CAUCHY_STIELTJES_POVM_E_WEYL_CAMERAS.md](</home/thlinux/Downloads/TRANSFORMADA_CAUCHY_STIELTJES_POVM_E_WEYL_CAMERAS.md>) | 75–111, 238–375, 377–485, 647–724 | Convenção anti-Herglotz, resolvente comprimido, inversa Weyl, separação `z0`, `λ`, `t` | Modelo útil para o sinal. Não contém identificação desses parâmetros ou desse readout com a altura nativa. |
| [C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md](</home/thlinux/Downloads/C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md>) | 81–159, 185–269 | Green C3 bruto em duas variáveis; derivação Wronskiano→Gram do estado de defeito | Identidade C3 específica localizada; derivação abstrata exige traces do mesmo estado. |
| [C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md](</home/thlinux/Downloads/C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md>) | 274–337 | Paridade via isometria do kernel e produto completado como soma de kernels | A soma de canais é útil, mas a fatorização positiva de cada canal é uma hipótese nessa etapa. |
| [C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md](</home/thlinux/Downloads/C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md>) | 496–589 | Revisão posterior da própria nota: campo Gamma já pronto; problema passa a readout compatível | Avanços posteriores já deram estado Gamma concreto no crosswalk. A comparação do bordo Cauchy com o Wronskiano nativo permanece separada. |
| [C2_GREEN_TFVD_RETORNO_DE_BORDO.md](</home/thlinux/Downloads/C2_GREEN_TFVD_RETORNO_DE_BORDO.md>) | 38–177 | Carta cross-Lagrangian, retorno por somas parciais e `I=GB+RTr` | Retorno finito explicitado, compatível com a ideia atual de reter bordo próprio. |
| [C2_GREEN_TFVD_RETORNO_DE_BORDO.md](</home/thlinux/Downloads/C2_GREEN_TFVD_RETORNO_DE_BORDO.md>) | 228–365 | Kernel do bulk incompleto, norma de grafo e proveniência apagada pelo quociente | Restrições de objetos específicos; há reparo algébrico atual por quociente de proveniência mínima. |
| [OBSERVACAO_DE_BORDO_ANGULAR_CONSERVATIVA(1).md](</home/thlinux/Downloads/OBSERVACAO_DE_BORDO_ANGULAR_CONSERVATIVA(1).md>) | 1–131, 133–320 | Órbita angular source-free, `Q_eff`, energia endpoint+retorno e complemento conservativo do observador | Mais uma apresentação concreta de energia preservada; não converte automaticamente órbita unitária em estado de defeito de parâmetro igual à altura. |
| [WEYL_RETURN_DEFECT_CANONICAL_STATE.md](</home/thlinux/Downloads/WEYL_RETURN_DEFECT_CANONICAL_STATE.md>) | 276–438, 607–731 | Mesmo raio misto por residual na métrica e defeito rank-one da Weyl inteira | Seleciona o retorno **não universal** do pacote fixo; não seleciona por si o observador nativo completo. |
| [Wayl/native_carry_registro_pesquisa_sondas_defeito_pt.md](</home/thlinux/Downloads/Wayl/native_carry_registro_pesquisa_sondas_defeito_pt.md>) | 1129–1286 | §20 acrescenta Weyl de alturas, momentos, fechamento de Green finito, alvo de fatoração geométrica | Variante ampliada e substancialmente distinta do registro PT raiz. A antiga frase “importa ξ como dado clássico externo” é datada: o autoadjunto atual já tem sua característica nativa. |

## 2. Identidade polarizada, com sinal verificado

**Hipóteses finitas:** `L=L*`, `P E=D`, `E*E+D*D=I`. Escrevo `D` para o bloco bulk para não confundi-lo com o readout resolvente `B(z)`.

$$
G_E=I+P^*P,
\qquad E^*G_EE=E^*E+(PE)^*(PE)=I.
$$

Defina, para parâmetros no resolvente,

$$
R_z=(zI-L)^{-1},\qquad S(z)=C R_z E^*,\qquad B(z)=C R_z C^*.
$$

**Derivação, sem hipótese de comutação extra:**

$$
\begin{aligned}
S(z)G_ES(w)^*
&=C R_z(E^*G_E E)R_w^*C^*\\
&=C R_zR_w^*C^*.
\end{aligned}
$$

Como `L=L*`, `R_w*=(bar(w)I−L)⁻¹`. A identidade do resolvente dá

$$
R_z-R_w^*=(\bar w-z)R_zR_w^*.
$$

Portanto, se `bar(w)≠z`,

$$
\boxed{
S(z)G_ES(w)^*=
\frac{B(z)-B(w)^*}{\bar w-z}.
}
$$

A forma sem divisão é válida sempre que ambos resolventes existem. Ela deve ser a primeira declaração; no encontro dos parâmetros reais, o kernel é `−B′(x)=C(xI−L)⁻²C*`. Em particular o sinal positivo corresponde ao `dslope` de **`−B`**.

Para uma fonte fixa `u`, ponha `b(z)=u*B(z)u`. A igualdade desejada com `a=−F′/(2F)` resultaria de

$$
a(z)=-b(z)+c,\qquad c\in\mathbb R,
$$

na mesma variável, mais identificação dos estados e normalização. Equivalentemente, `b(z)=F′(z)/(2F(z))+c`. Se a nota usa `m=−F′/F`, o kernel de `a=m/2` corresponde a dividir o vetor normalizado da nota por `sqrt(2)`.

**Atenção específica de tipagem:** `C`, `E` e `u` são fixos nessa dedução. Se a curva aritmética entra em uma fonte `u(t)` ou câmera `C(t)`, os produtos cruzados continuam bem definidos, mas não viram a diferença dividida de `u(t)*B(t)u(t)` por esta conta: aparecem as dependências adicionais do readout. É justamente onde procurar uma identidade com log-jets e bordo, em vez de igualar parâmetros por notação.

**Checagem independente:** SymPy no servidor, com matrizes racionais exatas `E=diag(3/5,5/13)`, `D=diag(4/5,12/13)`, `P=diag(4/3,12/5)`, `C=[[1,2],[3,4]]`, `L=diag(0,2)`, `z=1+i`, `w=3+2i`, produziu matrizes residuais exatamente nulas para a isometria, a covariância cruzada e o quociente acima. Isso confere um exemplo exato; a prova geral é a álgebra exibida, não o exemplo.

## 3. O que já está no Lean

Snapshot Weyl pesquisado: `248249ce098491f4194209d8e698dc5965f1405d`. As três primeiras declarações também foram localizadas na dependência efetivamente consumida pelo autoadjunto, pin `298d83c9351e308a5213b9f5ac32e44087f98a9f`; não é necessário atualizar a dependência para usá-las.

| Declaração | Fonte imutável | Hipóteses e alcance |
|---|---|---|
| `endpointMap_conjTranspose_mul_returnMetric_mul_endpointMap` | [ReturnMetric.lean:84–102](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/248249ce098491f4194209d8e698dc5965f1405d/NativeCarrySpectralWeyl/Finite/ReturnMetric.lean#L84-L102) | Matrizes finitas; recebe `P E=D` e `EᴴE+DᴴD=1`; prova `EᴴG_EE=1`. |
| `returnMetricCovariance_eq_directResolventCovariance` | [ReturnMetric.lean:104–131](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/248249ce098491f4194209d8e698dc5965f1405d/NativeCarrySpectralWeyl/Finite/ReturnMetric.lean#L104-L131) | `R` é matriz arbitrária, nem precisa ser resolvente. Cancela retorno e conserva a covariância completa. |
| `functionalReturnMetricCrossCovariance_eq_direct` | [FunctionalReturnMetric.lean:50–81](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/248249ce098491f4194209d8e698dc5965f1405d/NativeCarrySpectralWeyl/Finite/FunctionalReturnMetric.lean#L50-L81) | Observável arbitrário `O`; prova `C O R Eᴴ G_E (C R Eᴴ)ᴴ=C O R Rᴴ Cᴴ`, sem hipótese de comutação. |
| `tendsto_normalizedFiniteReturnMetricCovariance` / `tendsto_norm_normalizedFiniteReturnMetricCovariance_sub` | [FiniteDefectCovariance.lean:807–866](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/248249ce098491f4194209d8e698dc5965f1405d/NativeCarrySpectralWeyl/Limits/FiniteDefectCovariance.lean#L807-L866) | `Im z≠0`, câmeras ≥2, período comum positivo, e família que satisfaça as duas identidades em todo cutoff. Limite é `complexPeriodicGramMatrix`. |
| `c3RawGreenPairing_eq_eigenvalueDifference_mul_gammaGram` | [C3TwoVariableGreenGamma.lean:50–79](https://github.com/thiagomassensini/native-carry-c3-crosswalk/blob/1e9e06e1d51d176a909c187828f7c880e5d1207d/NativeCarryC3Crosswalk/C3TwoVariableGreenGamma.lean#L50-L79) | C3, todo cutoff e dois parâmetros complexos; fator é `3⁻ˢ−conj(3⁻ʳ)`, não `s−conj(r)` nem log-derivada de F. |
| `c3RawHeightGreenPairing_eq_eigenvalueDifference_mul_gammaGram` | [C3TwoVariableGreenGamma.lean:86–96](https://github.com/thiagomassensini/native-carry-c3-crosswalk/blob/1e9e06e1d51d176a909c187828f7c880e5d1207d/NativeCarryC3Crosswalk/C3TwoVariableGreenGamma.lean#L86-L96) | A mesma identidade após `s(z)=1/2+iz`. O fator continua a diferença dos autovalores da câmera. |
| `carryWeightedVerticalTfvd_identity` | [CpCarryWeightedVerticalTfvdIdentity.lean:61–72](https://github.com/thiagomassensini/primos/blob/e2a723b4ec3e645539de0b9ca881951d93259cda/CPFormal/Analytic/CpCarryWeightedVerticalTfvdIdentity.lean#L61-L72) | Para `0<q<1`, igualdade de CLMs `G_q B_q + R_q Tr_q = Id` no Hilbert vertical. |
| `minimalProvenance_factorization` | [CpMinimalProvenanceQuotient.lean:93–102](https://github.com/thiagomassensini/primos/blob/e2a723b4ec3e645539de0b9ca881951d93259cda/CPFormal/Analytic/CpMinimalProvenanceQuotient.lean#L93-L102) | O quociente por `ker Q ∩ ker A` retém simultaneamente ambos os mapas. Reparo algébrico concreto para o apagamento de proveniência da nota C2. |

Não localizei um lema público chamado “covariância de retorno com dois resolventes = diferença dividida”. Sua primeira metade já segue imediatamente do lema `EᴴG_EE=1`; alternativamente o lema funcional com `O=R_z R_w⁻¹` entrega a covariância cruzada. A segunda metade usa a identidade do resolvente. A ausência do nome não significa falta da peça algébrica.

**Detalhe importante da interface do limite:** o teorema de retorno citado fixa tipos finitos `endpoint` e `bulk` para todos os cutoffs, mas seu domínio espectral `Fin(finiteFamilyWindow cutoff camera)` cresce. Ele é uma implicação correta, e não instancia as coligações crescentes das notas. Em dimensões fixas, a isometria para todos os cutoffs não pode ser satisfeita quando a janela cresce. Para a família literal, a adaptação adequada é um corolário com tipos `endpoint M`, `bulk M`, usando o cancelamento finito em cada M e o limite direto já demonstrado. A correção é de interface; não exige uma nova estimativa analítica para a covariância direta.

O próprio [README atual:500–511](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/248249ce098491f4194209d8e698dc5965f1405d/README.md#L500-L511) explicita: a coligação precisa ser instanciada; álgebra funcional de grau arbitrário pronta; convergência funcional analítica demonstrada até grau oito, com indução de grau genérico ainda por completar. Assim o status das notas “todos os graus fechado por derivação” não deve ser transportado como “todos os graus já Lean”.

## 4. Passagem ao limite que serviria à costura SA3

Há dois limites distintos nas notas:

1. **Âncora de sonda fixa:** `S_M(z)G_EM S_M(z)* / A_M(z) → G_C`. O parâmetro `z` desaparece. Trata-se de uma métrica sobre as câmeras do pacote fixo; não de uma identidade nativa em duas alturas.
2. **Observável funcional preservado:** inserir `p(L_M−μ_M)` ou seu resolvente deixa no limite a variável espectral do multiplicador `Y=1+log x` no Hilbert da dilatação. Aqui continua existindo uma estrutura infinita em que graus polinomiais fazem sentido. Essa é a peça mais útil se for encontrada uma ligação explícita do observável com a altura nativa.

Uma rota suficiente para passar a identidade polarizada ao limite, a formalizar **depois** da identificação finita, é: para alturas reais regulares `x,z`, realizar todos os vetores em um Hilbert comum por isometrias `J_M` e provar `J_M Ψ̂_M(x)→Ψ̂(x)`, `J_M Ψ̂_M(z)→Ψ̂(z)` em norma. A continuidade do produto interno então conserva todos os cruzamentos. No outro lado, provar convergência do readout para `a`, incluindo a diagonal pela convergência de derivada ou regularidade local apropriada. Uma igualdade só na diagonal das sondas a uma âncora fixa não fornece essas duas alturas automaticamente.

Para usar o mapa atual diretamente, comparar com:

- `CanonicalCompletedC3ConcreteRealAxisPositiveSewing`, em [CompletedC3ConcreteRealAxisKernelCarrier.lean:266–274](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7b29b5938b58ffd45d34a3697536836c646291c1/CarrySelfAdjointOperator/CompletedC3ConcreteRealAxisKernelCarrier.lean#L266-L274): para todos M e reais x,z onde F≠0, readout final orientado = Gram do estado concreto.
- `canonicalCompletedC3RealAxisPositiveKernel_eq_sourceChannelSum`, no mesmo [arquivo:194–217](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7b29b5938b58ffd45d34a3697536836c646291c1/CarrySelfAdjointOperator/CompletedC3ConcreteRealAxisKernelCarrier.lean#L194-L217): soma exata das parcelas ordinária, log-jet e residual.
- `canonicalCompletedC3ConcreteRealAxisPositiveSewing_iff_realAxisKernel`, [arquivo:279–308](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7b29b5938b58ffd45d34a3697536836c646291c1/CarrySelfAdjointOperator/CompletedC3ConcreteRealAxisKernelCarrier.lean#L279-L308): equivalência, não prova da costura.

O estado concreto `Ψ⁺` já é o normalizado; o unnormalized do código é `sqrt(2) F · Ψ⁺`. Portanto comparar a covariância bruta com ele sem rastrear esse fator introduziria erro de escala.

**Alvo prático para buscar nas próximas notas:** uma fórmula de `C`, `E`, `P`, `λ(t)` e, se existir, `u(t)`, que mostre simultaneamente (i) o estado reconstruído completo é o estado nativo escolhido; (ii) o readout comprimido é `F′/(2F)` com sinal correto; (iii) as identidades com log-jets e o canal de completação acompanham o transporte; (iv) o limite das duas alturas é demonstrado. Nenhuma das notas desta seleção entregou os quatro itens juntos.

## 5. Correções e atualizações de claims antigos

### Geradora: correção confirmada por fonte mais completa

O registro PT raiz:376 e o EN correspondente imprimem

$$
(F_C(s))_{bc}=(m_0)_{bc}\frac{e^{s\ell_{bc}}}{1+s}.
$$

Da medida da própria nota,

$$
\begin{aligned}
(F_C(s))_{bc}
&=(m_0)_{bc}\int_0^{\ell_{bc}}e^{s(1+\log x)}dx\\
&=(m_0)_{bc}\frac{e^s\ell_{bc}^{s+1}}{1+s}
=(G_C)_{bc}\frac{e^{s(1+\log\ell_{bc})}}{1+s},
\qquad \Re s>-1.
\end{aligned}
$$

A expressão correta é exatamente a da nota analítica detalhada:411–422. Em `s=0`, dá `G_C=m_0 ℓ`; a derivada dá `G_C log ℓ`. O resumo errado dá `m_0` na ordem zero. Checagem simbólica independente dessas duas ordens: `ℓ` e `ℓ log ℓ` (antes de multiplicar por `m_0`). Não editei o original.

### No-go C2: condições preservadas, reparo posterior identificado

- A restrição “dois traces não bastam” é sobre o bulk que guarda **somente p nos centros pares**: seu kernel tem dimensão J+1. A própria nota já diz que promover a segunda diferença completa ou reter through-flow permite outro traço. Não é um no-go para toda válvula carry.
- A falta de bound do retorno de somas parciais é entre normas específicas do ledger (`ℓ²(h)` em arestas e `ℓ²` de vértices). Uma norma de grafo ou a geometria vertical ponderada constitui outro problema. Não foi extrapolada.
- O witness `Qg=0`, `Ag=(1−sqrt3)/2≠0` é uma conta exata para o quociente ali fixado. A solução formal posterior `X/(ker Q∩ker A)` conserva Q e A. Isso supera a ideia de que não haveria rota de proveniência, mantendo a validade do witness para o Q antigo. A identificação topológica/global com a curva nativa continua precisando de teorema específico.

### C3 e Gamma: a própria nota já contém revisão posterior

As seções 13–14 corrigem a versão inicial: o campo Gamma abstrato já existia. O crosswalk atual avança além disso com `seededCompletedTfvdCarryGammaState` e sua identidade diagonal. A nota de 20 de agosto não deve congelar o projeto em “construir um campo Gamma”. O alvo remanescente passa a ser a compatibilidade do bordo Cauchy desse estado com o Wronskiano completado; seu fornecimento não decorre só da igualdade `E*G_EE=I`.

O claim da nota §12 sobre uma formulação geral em p refere um arquivo e revisão histórica. No snapshot público C3 pesquisado, os teoremas `c3Raw...` citados acima são especializados à câmera 3. Não ampliei a quantificação desses nomes com base na prose antiga.

### Modo misto como estado escolhido

A nota `WEYL_RETURN...` prova simbolicamente que o defeito em relação a uma baseline universal está na direção fixa `P_*`; essa baseline e o setor de retorno não universal fazem parte da definição. Ela remove um simplex arbitrário **dentro desse setor**, mas não prova que o observador da característica nativa seja essa projeção. Para uso atual, procurar um teorema que identifique essa projeção com o canal residual do autoadjunto; não foi encontrado nesta seleção.

## 6. Duplicatas, versões e cronologia confiável

Há 20 arquivos na família de nomes examinada, 13 hashes distintos. Um mtime de Downloads pode ter sido alterado por cópia ou conversão; ele é evidência de arquivo, não data de descoberta. A nota C3 traz explicitamente “20 de agosto de 2026”.

- `WEYL_RETURN_DEFECT_CANONICAL_STATE.md`, `(1)` e `(2)` na raiz são idênticos byte a byte. A versão `Wayl/` tem hash diferente e restaura chaves e `\boxed` ausentes nas fórmulas; não contar as três cópias raiz como três descobertas.
- `C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md` raiz/hp/Wayl são byte a byte idênticos.
- `C2_GREEN_TFVD_RETORNO_DE_BORDO.md` raiz/tmp/TFVD são byte a byte idênticos.
- `CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md` raiz/FILTRO_HP são byte a byte idênticos.
- Os registros EN/PT raiz têm o mesmo desenvolvimento principal de 1091 linhas, em idiomas distintos. Não são hashes iguais.
- `hp/native_carry_registro_pesquisa_sondas_defeito_pt.md` tem 1262 linhas e a versão `Wayl/` 1286: **ambas acrescentam conteúdo sobre Weyl de alturas**, ausente do PT raiz. São variantes a preservar, não duplicatas para descarte. Comparando hp→Wayl, a versão Wayl acrescenta ainda às linhas 689–710 a Jacobi Meixner de profundidade C2: medida `∑_{k≥2}2^{1−k}δ_{k log 2}`, diagonal `3(n+1)log 2`, off-diagonal `sqrt(2)(n+1)log 2` e retorno de semigrupo; acrescenta o respectivo status na tabela. Essa diferença é conteúdo, não formatação.

Inventário completo com caminhos, SHA-256 e mtime: [inventario_retorno.json](inventario_retorno.json). A tabela abaixo fixa os originais prioritários; a data entre parênteses é mtime local, salvo quando marcado data textual.

| Arquivo relativo a Downloads | Linhas | SHA-256 | mtime local |
|---|---:|---|---|
| [CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md](</home/thlinux/Downloads/CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md>) | 979 | `c27ddb71bd16b4e704255aae9ff0eeee2509f40bafd11c63848268fe262ab45c` | 2026-08-12T13:20:24 |
| [LIMITE_FRAME_DEFECT_PROBES_SEM_COLAPSO.md](</home/thlinux/Downloads/LIMITE_FRAME_DEFECT_PROBES_SEM_COLAPSO.md>) | 586 | `2c4559bbbcb409b1aaec3d2f0efd9be489255c6ff89cf789712963b2e87b36ed` | 2026-08-12T13:20:24 |
| [WEYL_RETURN_DEFECT_CANONICAL_STATE (1).md](</home/thlinux/Downloads/WEYL_RETURN_DEFECT_CANONICAL_STATE (1).md>) | 811 | `20452b9e3a5a0e14b60b4c30ed8ffcf4ecb157bfb85c7cc096aca81aac511c17` | 2026-08-12T13:20:24 |
| [C2_GREEN_TFVD_RETORNO_DE_BORDO.md](</home/thlinux/Downloads/C2_GREEN_TFVD_RETORNO_DE_BORDO.md>) | 376 | `83312aaeca9d65a481934b9bb1dce20763d84eac004c52e36b4a93d3d0ec1b96` | 2026-08-12T13:20:24 |
| [C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md](</home/thlinux/Downloads/C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md>) | 606 | `e8c8e62ad78535f7c881630ae55e67fff92534947256b52d968c7ce82970cbf1` | 2026-08-30T01:56:29 |
| [UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md](</home/thlinux/Downloads/UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md>) | 563 | `fa4c1cf63b1db8df4367268947dede9a3aa06759763297de895ebd83dcc879e3` | 2026-08-12T13:20:24 |
| [native_carry_defect_probe_research_log.md](</home/thlinux/Downloads/native_carry_defect_probe_research_log.md>) | 1091 | `1086d4dc67a135ce46faf318523c84679920a2a03111b2bc4e110e4be89a9f97` | 2026-09-04T20:44:22 |
| [WEYL_RETURN_DEFECT_CANONICAL_STATE.md](</home/thlinux/Downloads/WEYL_RETURN_DEFECT_CANONICAL_STATE.md>) | 811 | `20452b9e3a5a0e14b60b4c30ed8ffcf4ecb157bfb85c7cc096aca81aac511c17` | 2026-08-12T13:20:24 |
| [native_carry_registro_pesquisa_sondas_defeito_pt.md](</home/thlinux/Downloads/native_carry_registro_pesquisa_sondas_defeito_pt.md>) | 1091 | `64228e4e1baa9d0da6a59949226b0639f22619dcc08974bbc0b443a4e129432a` | 2026-08-12T13:20:24 |
| [WEYL_RETURN_DEFECT_CANONICAL_STATE (2).md](</home/thlinux/Downloads/WEYL_RETURN_DEFECT_CANONICAL_STATE (2).md>) | 811 | `20452b9e3a5a0e14b60b4c30ed8ffcf4ecb157bfb85c7cc096aca81aac511c17` | 2026-08-12T13:20:24 |
| [hp/C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md](</home/thlinux/Downloads/hp/C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md>) | 606 | `e8c8e62ad78535f7c881630ae55e67fff92534947256b52d968c7ce82970cbf1` | 2026-08-28T07:00:53 |
| [hp/native_carry_registro_pesquisa_sondas_defeito_pt.md](</home/thlinux/Downloads/hp/native_carry_registro_pesquisa_sondas_defeito_pt.md>) | 1262 | `c10240222be41d909db5e6cf3fd45078eeaef5a5d3fc82998598d104b4c436ed` | 2026-08-28T07:00:53 |
| [tmp/C2_GREEN_TFVD_RETORNO_DE_BORDO.md](</home/thlinux/Downloads/tmp/C2_GREEN_TFVD_RETORNO_DE_BORDO.md>) | 376 | `83312aaeca9d65a481934b9bb1dce20763d84eac004c52e36b4a93d3d0ec1b96` | 2026-07-19T19:48:28 |
| [FILTRO_HP/CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md](</home/thlinux/Downloads/FILTRO_HP/CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md>) | 979 | `c27ddb71bd16b4e704255aae9ff0eeee2509f40bafd11c63848268fe262ab45c` | 2026-08-12T13:20:24 |
| [Wayl/C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md](</home/thlinux/Downloads/Wayl/C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md>) | 606 | `e8c8e62ad78535f7c881630ae55e67fff92534947256b52d968c7ce82970cbf1` | 2026-08-30T03:56:15 |
| [Wayl/UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md](</home/thlinux/Downloads/Wayl/UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md>) | 563 | `6580eee5ab63133019117ace3a505e8634b1404d96620fd1f07e43652d215d4b` | 2026-08-30T03:56:15 |
| [Wayl/native_carry_defect_probe_research_log.md](</home/thlinux/Downloads/Wayl/native_carry_defect_probe_research_log.md>) | 1091 | `8be81ba74d53aa9b77807c050c74b0f8df2ba2476b56bfe237134aa1b8914f5f` | 2026-08-30T03:56:15 |
| [Wayl/WEYL_RETURN_DEFECT_CANONICAL_STATE.md](</home/thlinux/Downloads/Wayl/WEYL_RETURN_DEFECT_CANONICAL_STATE.md>) | 811 | `a1f75410109ea66448725a041e90ca8099e35f5fdf654b52aa09b6407e6bf1e1` | 2026-08-30T03:56:15 |
| [Wayl/native_carry_registro_pesquisa_sondas_defeito_pt.md](</home/thlinux/Downloads/Wayl/native_carry_registro_pesquisa_sondas_defeito_pt.md>) | 1286 | `ceacbdce6b75fe057c70baaf835d65b34edc3cd27804df4a4bf1811d94717294` | 2026-08-30T03:56:15 |
| [TFVD/C2_GREEN_TFVD_RETORNO_DE_BORDO.md](</home/thlinux/Downloads/TFVD/C2_GREEN_TFVD_RETORNO_DE_BORDO.md>) | 376 | `83312aaeca9d65a481934b9bb1dce20763d84eac004c52e36b4a93d3d0ec1b96` | 2026-07-19T17:25:17 |

## Precisões da revisão independente

Se o parâmetro geométrico for $\lambda(t)$, o kernel do resolvente tem denominador $\lambda(z)-\lambda(x)$. Para $a(t)=-b(\lambda(t))+c$, surge o fator $\operatorname{dslope}\lambda(x,z)$ ao passar para a diferença dividida na altura. No caso afim crescente ele é absorvido por uma escala constante dos vetores; no caso não linear pede uma identidade adicional. A condição $F(t)\ne0$ também não prova sozinha que $\lambda(t)$ esteja no resolvente de $L$.

O limite com tipos de endpoint fixos não realiza janelas ilimitadas: $E^*G_EE=I$ já implica que $E$ é injetivo. Uma família dependente do cutoff pode usar o cancelamento finito e o limite direto com o pacote de câmeras ainda fixo; fazer esse pacote também crescer é outra etapa.

## 7. Próxima ordem de trabalho recomendada

1. Reutilizar o cancelamento de retorno já formalizado e escrever a versão polarizada sem divisão; adaptar a interface de famílias com dimensões variáveis se a construção exigir cutoffs crescentes.
2. Extrair das notas uma realização **concreta** do readout nativo e calcular seu defeito em relação ao Gram SA3, começando pela diagonal em zero e pelas primeiras entradas; incorporar log-jets, residual e normalização.
3. Se o defeito zerar com prova estrutural, conectar o transporte/limite já disponível e consumir o certificado existente. Se não zerar para essa realização, guardar a expressão exata e investigar a métrica/readout alternativos sugeridos pelas notas, sem transformar o teste específico em veto à rota inteira.

[Voltar ao mapa principal](../mapa-notas-costura-energia-momentos-carry.md).

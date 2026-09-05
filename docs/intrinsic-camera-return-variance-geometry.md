# Mapa — geometria intrínseca do retorno e da variância

Data: 2026-09-05

Repositório: thiagomassensini/carry-self-adjoint-operator

Base desta rodada: 3674c8feeb0e2b2ef26afe6a0cd9df786ce790fe, descendente da base pedida 225a85d9e8e3e0a3b659c5b6ad821458770b3195.

Branch: agent/camera-return-variance-geometry.

## O que a geometria está construindo

A estrutura que aparece das definições é um sistema de análise e reconstrução que conserva a métrica completa, admite diferentes observadores e cresce com o atlas de câmeras. O defeito misto é uma parte distinguida desse sistema. Sua importância não exige que ele sozinho represente todos os estados ou todos os readouts.

Nesta rodada seguimos as matrizes e os perfis já existentes, sem escolher uma característica espectral como destino. Encontramos três fatos concretos e os verificamos no Lean:

1. A amplitude do defeito de retorno e a amplitude da variância, consideradas juntas, preservam a energia, todos os produtos cruzados reais e o vetor de entrada.
2. O trace finito de valor tem uma direção dual determinada por G. Ela contém tanto o raio misto quanto a câmera 7, com coeficientes exatos.
3. O defeito cru deixa de ser de rank no máximo um já no atlas 2,3,6,8. Um menor vale exatamente −48(log 2)².

Nenhum desses resultados identifica o Gram Gamma com o dslope nativo. Eles descrevem o que a geometria fornece antes dessa pergunta.

## 1. Origem: representação, quantidade e câmera

A cadeia de origem continua sendo a representação posicional. O teorema arithmeticCarryUniversality reúne a contagem de estados, a classe saturada de carry, a massa crítica, a rigidez quadrática e a compatibilidade entre bases. O peso não é uma calibração espectral.

Na camada TFVD, nativeGpreFiniteTfvdReconstruction_comp_analysis já demonstra reconstrução exata a partir da análise que mantém os dados de bordo e de proveniência. Isso fornece um padrão útil para a leitura desta rodada: uma observação parcial pode ser insuficiente enquanto o pacote completo continua fiel.

No lado das câmeras, os perfis periódicos determinam a média de produto m e a matriz

$$
G_{bc}=\min(\ell_b,\ell_c)\,m_{bc}.
$$

O alinhamento da câmera 2 dá $\ell_2=4$; nas demais câmeras consideradas, $\ell_b=b$. A correlação m é calculada nos mesmos resíduos completos, com período comum. Usamos 420 para o pacote 2,3,4,5,6,7 e 24 para o atlas 2,3,6,8.

G mede produtos entre câmeras; ela não foi definida como matriz dos momentos nativos de altura.

## 2. A conservação que o retorno sozinho não mostrava

Mantemos exatamente as matrizes existentes:

$$
T=\operatorname{diag}(\log\ell_b),\qquad
A=G^{-1/2}(H-GT)G^{-1/2},
$$

$$
V=G^{-1/2}(J-HG^{-1}H)G^{-1/2}.
$$

A ordem H−GT é essencial. A não é, em geral, um projetor ortogonal.

A formalização anterior já continha a identidade do defeito e a positividade da variância do pacote de seis câmeras. A nova combinação dá

$$
\boxed{A^*A+V=I,\qquad V\ge0.}
$$

Tomando a raiz positiva intrínseca $S=\sqrt V$, obtemos, sem ajustar um escalar,

$$
\boxed{\langle Au,Av\rangle+\langle Su,Sv\rangle=\langle u,v\rangle,}
$$

$$
\boxed{u=A^*(Au)+S^*(Su).}
$$

Portanto a análise $u\mapsto(Au,Su)$ é injetiva e conserva o produto interno. Na coordenada original de coeficientes, $u=G^{1/2}c$, o produto recuperado é exatamente $c^TGd$, inclusive os termos fora da diagonal.

Se $Au=0$, então

$$
Vu=u,\qquad \|Su\|^2=\|u\|^2.
$$

Isso localiza as direções antes chamadas de cegas ao retorno: sua energia permanece integralmente no canal de variância. Os pulsos completos de início/câmera 5 e fim/câmera 7, com suas pernas radiais, foram verificados explicitamente.

Aqui “defeito de retorno” designa A e seu quadrado I−V. Nas notas de Weyl, V também aparece como coeficiente de retorno da expansão inversa. Essa diferença de nomenclatura não deve apagar nenhum dos dois termos positivos.

**Lean novo:** sixCamera_return_variance_partition, sixCamera_return_variance_reconstruction, sixCamera_return_variance_polarization, sixCamera_return_variance_pair_injective, sixCamera_return_variance_source_gram, c3LastPulse_variance_fixed e c3InitialPulse_variance_fixed.

## 3. O centramento que a própria fronteira da câmera determina

Há uma identidade anterior à escolha de seis câmeras, agora registrada para qualquer família finita:

$$
\boxed{J-HT-TH+TGT=G.}
$$

Ela decorre das fórmulas exatas dos momentos:

$$
H_{bc}=G_{bc}\log\min(\ell_b,\ell_c),
$$

$$
J_{bc}=G_{bc}\bigl(1+\log^2\min(\ell_b,\ell_c)\bigr).
$$

O mecanismo é o mínimo dos suportes: um dos fatores
$\log\min(\ell_b,\ell_c)-\log\ell_b$ e
$\log\min(\ell_b,\ell_c)-\log\ell_c$ é zero. Assim, os cruzamentos também fecham.

**Lean novo:** camera_boundaryCentered_momentGram_eq_gram. A prova reutiliza camera_secondMoment_sub_gram_eq_slope_identity.

A interpretação vetorial a seguir é uma dedução das fórmulas integrais existentes; nesta rodada formalizamos sua identidade matricial, sem criar outro operador.

Na realização Naimark já disponível, escreva

$$
\phi_b(x)=\mathbf1_{(0,\ell_b]}(x)\,r_b,\qquad
\langle r_b,r_c\rangle=m_{bc}.
$$

O perfil logarítmico centrado no bordo de cada câmera é

$$
\eta_b(x)=\bigl(1+\log x-\log\ell_b\bigr)\phi_b(x).
$$

Ele tem a mesma matriz de Gram que $\phi_b$. Se E é a síntese das $\phi_b$ e Y é a multiplicação já existente por $1+\log x$, então, em um atlas com G invertível,

$$
U=EG^{-1/2},\qquad D=(YE-ET)G^{-1/2}
$$

satisfazem

$$
U^*U=D^*D=I,\qquad U^*D=A,
$$

$$
D^*(I-UU^*)D=V.
$$

Essas fórmulas explicam a decomposição: A mede a compressão da descrição logarítmica centrada sobre a descrição original; V mede a parcela ortogonal que essa compressão não registra. A geometria já contém as duas parcelas.

Não afirmamos ter construído uma extensão única de D a todas as bases, nem uma identificação desse D com o Gamma completado. Isso exigiria verificar os respectivos domínios e mapas de transporte.

## 4. O trace escolhe sua própria direção dual

A ordem das coordenadas é 2,3,4,5,6,7. No porto finito de Green, os coeficientes completos têm a forma

$$
c=(r g_0,r g_1,r g_2;\ g_0,g_1,g_2).
$$

A parte linear do trace horizontal de valor é $g_2-g_1=c_7-c_6$, onde os subscritos 6 e 7 aqui são os rótulos das câmeras.

Para representá-la com a própria métrica, resolvemos a equação de Riesz

$$
Gq=e_7-e_6.
$$

O resultado exato é

$$
q=\left(\frac9{139},\frac9{278},-\frac3{139},0,
-\frac9{278},\frac1{42}\right)
=-\frac3{278}v_*+\frac1{42}e_7.
$$

Consequentemente,

$$
\boxed{q^TGc=c_7-c_6,\qquad q^TGq=\frac{164}{2919}.}
$$

Não ajustamos esses números para reproduzir um momento: eles são impostos pela matriz G e pelo trace existente. As direções $v_*$ e $e_7$ são G-ortogonais; suas normas quadradas são 278 e 42. Em coordenadas Hilbert unitárias, a mesma decomposição lê-se

$$
q_H=-\frac3{\sqrt{278}}p_*+\frac1{\sqrt{42}}p_7.
$$

A última escrita é a tradução das identidades matriciais pelos embeddings isométricos existentes. Os novos teoremas verificam diretamente a equação dual, a decomposição, a norma e o readout em coeficientes reais.

Isso explica geometricamente a obstrução anterior: o raio misto isolado não observa a componente da câmera 7 exigida por esse trace. A métrica completa observa ambas.

Este cálculo trata da parte finita de valor. O trace completado ainda mantém constante de reconstrução, tail, jets e completion nas identidades anteriores. Eles não foram removidos nem absorvidos em q.

**Lean novo:** sixCamera_valueTrace_dual_equation, sixCamera_valueTrace_dual_decomposition, sixCamera_valueTrace_dual_norm_sq e sixCamera_valueTrace_dual_readout.

## 5. Ao ampliar o atlas, aparece outra direção de retorno

O rank um do pacote de seis câmeras não deve ser promovido a uma regra global. Para testar o que a própria representação faz, mantivemos os mesmos perfis e acrescentamos a câmera 8.

Basta observar o subatlas 2,3,6,8, com período comum 24. As médias periódicas exatas dão

$$
m_{2,8}=2,\qquad m_{3,6}=2,\qquad m_{3,8}=0.
$$

Para o numerador cru $N=H-GT$, o menor nas linhas 2,3 e colunas 6,8 tem a forma

$$
\begin{pmatrix}
N_{2,6} & 8(\log4-\log8)\\
6(\log3-\log6) & 0
\end{pmatrix}.
$$

O primeiro elemento nem precisa ser estimado: seu cofator é zero. Logo,

$$
\boxed{\det N_{\{2,3\},\{6,8\}}=-48(\log2)^2\ne0.}
$$

A prova usa os perfis inteiros, aritmética exata e $\log2>0$. Não usa estimativa decimal de autovalores nem tolerância numérica.

**Lean novo:** cameras2368_returnNumerator_minor, cameras2368_returnNumerator_minor_ne_zero e cameras2368_returnNumerator_not_rank_one.

O último enunciado exclui exatamente uma fatoração $N=u v^T$ nesse atlas. O menor certifica pelo menos duas direções no defeito cru. Não demonstra crescimento ilimitado do rank, nem independência infinita de jets. O fato novo é que a expansão do atlas já produz uma estrutura maior que o raio misto inicial.

## 6. O objeto natural que já está disponível

O desenvolvimento existente chega a um Hilbert de câmeras, à sua dilatação Naimark, à medida de operadores positiva normalizada e ao operador logarítmico. A sequência de construções é:

~~~text
perfis posicionais completos
    → correlações periódicas e Gram G
    → CameraHilbert e realização Naimark
    → medida positiva de operadores
    → leituras vetoriais, escalares e Cauchy/Weyl
~~~

A nova conservação fornece uma leitura complementar dentro dessa sequência:

~~~text
coeficientes c → u = sqrt(G)c
                    ├─ A u        : amplitude do defeito de retorno
                    └─ sqrt(V) u  : amplitude da variância
                  ambas → produto interno e reconstrução exatos
~~~

O observador vem depois: o trace possui seu dual q; o modo misto possui sua direção; uma resultante dinâmica possui seus fatores de câmera. O espaço comum e a reconstrução permitem comparar essas leituras mediante mapas demonstrados. Não tornam leituras diferentes automaticamente iguais.

A multiplicação logarítmica e a transformada Cauchy já estão implementadas. Não criamos outra Jacobi, outro Gamma, outra sequência de momentos ou outro operador autoadjunto.

## 7. Coordenadas e limites que continuam separados

| Símbolo/camada | Significado nesta investigação |
| --- | --- |
| b e profundidade k | Representação posicional e escala do carry |
| c | Coeficientes de síntese no porto/câmeras |
| χ(s) | Resultantes dinâmicas das câmeras; não se postulou χ=Gc |
| x no Naimark | Coordenada positiva do suporte dos perfis |
| y=1+log x | Coordenada do operador logarítmico já existente |
| t em s=1/2+it | Parâmetro angular/altura na família nativa |
| λ | Parâmetro de resolvente; não foi identificado com t |
| G,H,J desta rodada | Momentos das câmeras, não os h_n nativos de altura |

O centramento logarítmico dependente do cutoff também tem origem demonstrada: tendsto_resolventLogMean_sub_log_add_one prova que a média de log n é assintoticamente log M−1 na construção correspondente. Isso dialoga com o centramento de bordo, mas não identifica automaticamente todos os limites, medidas e parâmetros.

A nota dinâmica e as notas de limite orientam a comparação. As afirmações que ainda não têm o mapa Lean correspondente permanecem deduções ou tarefas de formalização.

## 8. Localização das peças e estatuto

Todos os arquivos novos abaixo estão no módulo [CameraReturnVarianceEnergyBalance.lean](../CarrySelfAdjointOperator/CameraReturnVarianceEnergyBalance.lean).

| Peça | Fonte exata | Uso e estatuto |
| --- | --- | --- |
| Massa, amplitude e compatibilidade entre bases | [CarryGeometry/Universality.lean](https://github.com/thiagomassensini/carry-geometry/blob/1f85b8c3ab5ded27a0782956e1ada0dd8a1b6fd4/CarryGeometry/Universality.lean), arithmeticCarryUniversality | Teorema existente no pin consumido |
| Análise/reconstrução TFVD | [CPFormal/Analytic/CpNativeGpreTfvdAnalysis.lean](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpNativeGpreTfvdAnalysis.lean), nativeGpreFiniteTfvdReconstruction_comp_analysis | Teorema existente; preserva os dados do porto |
| Persistência de readout | [CPFormal/Logic/StructuralPersistence.lean](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Logic/StructuralPersistence.lean), minimal_view_invariance | Exige a estrutura e a validade do atlas certificadas |
| Perfis periódicos | [NativeCarrySpectralWeyl/Camera/PeriodicProfiles.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Camera/PeriodicProfiles.lean) | Definições aritméticas reutilizadas sem alteração |
| Gram e momentos | [NativeCarrySpectralWeyl/Finite/Gram.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Finite/Gram.lean) e [Moments.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Finite/Moments.lean) | Base exata dos cálculos novos |
| Positividade da variância | [NativeCarrySpectralWeyl/Finite/StepDensity.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Finite/StepDensity.lean), sixCameraVariance_posSemidef | Teorema existente, incondicional para as seis câmeras |
| Fatorização do retorno | [CameraReturnVarianceDefect.lean](../CarrySelfAdjointOperator/CameraReturnVarianceDefect.lean) | Teoremas existentes com a orientação H−GT |
| Conservação completa e dual do trace | CameraReturnVarianceEnergyBalance.lean | Novos teoremas desta rodada |
| Segundo modo no atlas 2,3,6,8 | cameras2368_returnNumerator_not_rank_one | Novo certificado exato; não afirma rank ilimitado |
| Medida normalizada | [NativeCarrySpectralWeyl/Finite/StepPOVM.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Finite/StepPOVM.lean), sixCameraStepPOVM e sixCameraCenteredLogPOVM | Construções existentes, massa total I |
| Hilbert e dilatação | [NativeCarrySpectralWeyl/Infinite/Kolmogorov.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Infinite/Kolmogorov.lean) e [Naimark.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Infinite/Naimark.lean) | Construções existentes com produtos internos exatos |
| Operador logarítmico | [NativeCarrySpectralWeyl/Infinite/LogarithmicMultiplication.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Infinite/LogarithmicMultiplication.lean) | Operador de multiplicação existente; domínio explícito |
| Cauchy e Weyl inverso | [NativeCarrySpectralWeyl/Infinite/Cauchy.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Infinite/Cauchy.lean) e [WeylInverse.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Infinite/WeylInverse.lean) | Inverso na imagem densa; não inverso limitado global postulado |
| Extensão de readout Green–Haar | [NativeCarrySpectralWeyl/Boundary/GreenHaarCameraForm.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Boundary/GreenHaarCameraForm.lean) | Infraestrutura de extensão limitada; não a igualdade Gamma/native |
| Fatores modais dinâmicos | [NativeCarrySpectralWeyl/Camera/ModalEnergy.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Camera/ModalEnergy.lean), modalEnergy_eq_modalWeight_mul_nativeScalar_normSq | Identidade dos objetos ali definidos; não supõe χ igual ao porto completo |
| Centramento móvel | [NativeCarrySpectralWeyl/Limits/ResolventLogMean.lean](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Limits/ResolventLogMean.lean) | Teorema assintótico existente |
| Pulsos cegos ao retorno e trace completado | [C3ReturnCompletedTraceChannels.lean](../CarrySelfAdjointOperator/C3ReturnCompletedTraceChannels.lean) | Obstruções anteriores reutilizadas para localizar energia preservada |

Pins consultados e preservados:

- NativeCarrySpectralWeyl: 298d83c9351e308a5213b9f5ac32e44087f98a9f.
- CarryGeometry: 1f85b8c3ab5ded27a0782956e1ada0dd8a1b6fd4.
- NativeCarryC3Crosswalk: 150cfc7fb08da96bf8117f15869cc2b819d593c2.
- CPFormal: 65d50f6db1208708e109982ba97e1d51d3039956.
- GreenFrame: cd2d838bee67ad23f869a02f8ed9f0a0feb926fa.

O arquivo WeightedTransform mencionado em mapas anteriores não está nesse pin de CarryGeometry. Nenhum resultado de um pin mais novo foi importado silenciosamente.

### Notas usadas como guia

- WEYL_RETURN_DEFECT_CANONICAL_STATE.md: interpretação do retorno universal e do defeito misto; confrontada com as matrizes Lean.
- NATIVE_CARRY_DYNAMIC_SECTOR_LIMIT_THEOREM.md: resultantes, fatores de câmera e jets; mantidos distintos dos coeficientes do porto.
- TRANSFORMADA_CAUCHY_STIELTJES_POVM_E_WEYL_CAMERAS.md: medida positiva, whitening e coordenada logarítmica; confrontados com StepPOVM e Naimark.
- hp/ATLAS_RELACIONAL_MESTRE_PERSISTENCIA_ESTRUTURAL.md: reconstrução e transporte do ledger; comparados com StructuralPersistence e a análise TFVD existente.
- LIMITE_FRAME_DEFECT_PROBES_SEM_COLAPSO.md: separação dos parâmetros e centramento móvel; conferida a implementação do limite em ResolventLogMean.

Essas notas estão em /home/thlinux/Downloads. Seus rótulos históricos de fechamento ou pendência não foram usados como premissas. O estatuto indicado neste mapa vem das declarações efetivamente consultadas no pin consumido.

## 9. Próximas perguntas que nascem da geometria

1. Formalizar no Naimark existente os perfis centrados η_b e a identidade entre suas sínteses, usando a igualdade matricial agora verificada. A tarefa concreta é transportar o Gram preservado para a realização vetorial já disponível e controlar seus domínios.
2. Classificar os novos setores ao crescer o atlas. O menor 2,3 × 6,8 fornece um primeiro certificado exato; o passo seguinte é descrever que relações de divisibilidade e suporte abrem ou preservam cada direção.
3. Transportar os readouts completos pela análise $(A,\sqrt V)$, começando pelo dual q do trace finito e mantendo separadas as demais componentes de bordo e jets.
4. Só após esses transportes, comparar as leituras produzidas pelo mesmo estado. A igualdade com o dslope nativo continua uma pergunta específica, com seu defeito explícito já tipado.

Estas perguntas não exigem supor que toda a geometria deva convergir para uma única medida ou um único canal escalar.

## 10. Validação e limites desta entrega

O módulo novo tem 20 teoremas públicos e dois lemas privados auxiliares. Ele foi integrado no aggregator, Audit e KernelConstructionAudit. A validação final fica registrada em [research/camera-return-variance-geometry-2026-09-05](../research/camera-return-variance-geometry-2026-09-05/).

**Validação concluída:** 14/14 estágios de scripts/audit.sh passaram, com exit code 0 e sem warnings; os 20 novos teoremas passaram em #check e #print axioms. O conjunto transitivo dos axiomas usados está contido em {propext, Classical.choice, Quot.sound}, sem sorryAx. Os 15 pins de dependências e oito arquivos-base foram conferidos sem alteração.

Nenhuma hipótese matemática nova foi introduzida para os resultados concretos. Os enunciados condicionais sobre um vetor no núcleo de A explicitam essa condição como premissa local; as identidades de conservação e os certificados concretos são incondicionais. Não há nova definição global de operador, momento, Jacobi ou Gamma.

A identificação Gamma/native Gram não foi obtida nesta rodada e não é uma premissa de qualquer prova nova. Conservar a métrica G também não corrige, por si só, a incompatibilidade já demonstrada para o Gamma atual: a nova análise preserva essa métrica. A branch permanece separada, sem merge.

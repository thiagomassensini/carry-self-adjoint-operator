# Mapa — defeito de retorno da Weyl e seleção geométrica da fonte

Conferência de 2026-09-05 a partir do grep de Thiago por `1,1,1,1`. Base do branch: `2054a1c3b86546f19844948a77265fd3272ef49e`.

## 1. O que a pista acrescenta

**O defeito do retorno universal fornece um mecanismo geométrico para selecionar uma fonte.** No pacote de câmeras $\{2,3,4,5,6,7\}$, a nota identifica o mesmo raio por duas construções: o setor excepcional da variância da Weyl e o resíduo da câmera 6 na métrica de retorno. Isso torna a escolha da direção da fonte concreta.

Nesta rodada, a fatorização positiva do defeito foi demonstrada em Lean a partir dos Grams e momentos já formalizados. O vetor residual e seu comprimento também foram verificados. A identificação desse mecanismo com os momentos nativos de altura permanece aberta.

| Ocorrência do grep | Significado dos “uns” | Uso nesta rota |
| --- | --- | --- |
| `WEYL_RETURN_DEFECT_CANONICAL_STATE`, registros de sondas, `INVARIANCIA_C2_HAAR_DUPLO_LOG4` | Variância unitária dos cinco graus puros | Selecionar o defeito relativamente ao retorno universal |
| `FOURIER_GALOIS_DEFEITO_CENTRADO_RODAS_CARRY` | Valores do perfil centrado $1-p\mathbf1_{p\mid n}$ fora da classe de carry | Origem dos perfis e das correlações periódicas |
| `teoria_defeitos_c2_unificada` | Multiíndices de expoentes na fatoração de inteiros | Cumulantes de produtos de primos; não são autovalores da variância |
| `ONTOLOGIA_DA_PRESENCA_CAUSAL` | Indicadores de um perfil conceitual de existência | Coincidência textual, sem objeto espectral correspondente |

Várias ocorrências são cópias. As três notas `WEYL_RETURN_DEFECT_CANONICAL_STATE` na raiz de Downloads têm o mesmo hash; as três cópias indicadas da nota C2/Haar também. A versão em `Downloads/Wayl/WEYL_RETURN_DEFECT_CANONICAL_STATE.md` conserva melhor os delimitadores das fórmulas. Nenhum original foi alterado.

## 2. Da métrica de câmeras à energia do defeito

As matrizes de entrada são as já formalizadas no pacote `NativeCarrySpectralWeyl`, pin `298d83c9351e308a5213b9f5ac32e44087f98a9f`:

$$
G_{ij}=m_{ij}\min(\ell_i,\ell_j),\quad
H_{ij}=G_{ij}\log\min(\ell_i,\ell_j),\quad
J_{ij}=G_{ij}\bigl(1+\log^2\min(\ell_i,\ell_j)\bigr).
$$

Aqui $\ell_2=4$ e $\ell_b=b$ para as demais câmeras do pacote. O período comum $420$ produz exatamente a matriz racional de seis câmeras; `sixCameraGram_eq` e `sixCameraGram_posDef` já estavam demonstrados.

Com $T=\operatorname{diag}(\log\ell_i)$, a identidade de cada entrada dá

$$
J-G=TH+HT-TGT.
$$

Logo, para $G$ positivo definido,

$$
D:=G-J+HG^{-1}H
=(TG-H)G^{-1}(GT-H).
$$

Escreva $R=G^{-1/2}$, $L=RHR$ e $\mathscr V=RJR-L^2$. O operador explícito

$$
A=R(H-GT)R
$$

satisfaz

$$
\boxed{I-\mathscr V=A^*A\succeq0.}
$$

**Essa fatorização agora está no Lean.** Ela conserva a correção completa $HG^{-1}H$ e todos os cruzamentos. Não consiste em subtrair uma constante de uma norma escolhida depois.

O novo [CameraReturnVarianceDefect](../CarrySelfAdjointOperator/CameraReturnVarianceDefect.lean) contém:

| Declaração | Garantia |
| --- | --- |
| `camera_secondMoment_sub_gram_eq_slope_identity` | Identidade dos momentos para qualquer família finita de perfis |
| `camera_varianceDefect_factorization` | Fatorização de $D$ na ordem correta |
| `one_sub_varianceOperator_eq_returnCompression_square` | $I-\mathscr V=A^*A$ sob a identidade dos momentos |
| `camera_one_sub_variance_eq_return_square` | Aplicação aos momentos efetivamente definidos pelas câmeras |
| `sixCamera_one_sub_variance_posSemidef` | Positividade no pacote concreto, sem nova hipótese de positividade |
| `sixCameraGram_mul_mixedReturnRay` | $Gv_*=(278/3)e_6$ |
| `sixCameraMixedReturnRay_gram_norm_sq` | $v_*^TGv_*=278$ |

A interpretação de $A$ como compressão de um unitário Hardy–Cayley aparece na nota de composicionalidade. O módulo desta rodada prova a expressão matricial e sua energia; não acrescenta uma formalização dessa dilatação infinita.

## 3. A fonte selecionada pelas seis câmeras

Na ordem $(2,3,4,5,6,7)$,

$$
v_*=(-6,-3,2,0,3,0)^T,\qquad
r_6=\tfrac13v_*=e_6-(2e_2+e_3-\tfrac23e_4).
$$

Os dois últimos teoremas mostram que esse raio é $G$-ortogonal aos outros cinco eixos e tem comprimento conhecido. A direção unitária em coordenadas whitened é

$$
p_*=\frac{G^{1/2}v_*}{\sqrt{278}},\qquad P_*=p_*p_*^*.
$$

A auditoria simbólica exata, separada da verificação Lean, obteve

$$
D=\frac{4Q}{139}e_6e_6^T,\qquad
Q=457\log^22-512\log2\log3+304\log^23,
$$

$$
I-\mathscr V=\delta P_*,\qquad
\delta=\frac{18Q}{19321}=1-\rho_*\approx0.183150308474604.
$$

A matriz da forma $Q$ tem determinante $73392>0$ e primeiro menor $457>0$, portanto $Q>0$ no vetor $(\log2,\log3)$. Assim, a normalização pelo traço seleciona $P_*$. A unicidade é a do estado positivo de traço um suportado nesse raio; não identifica automaticamente todo observador do sistema com esse estado.

## 4. Medida e kernel disponíveis para essa fonte

A contração dos perfis pela direção $v_*$, normalizada por $278$, reproduziu exatamente a medida das notas:

$$
d\nu_*(x)=\frac1{139}
\begin{cases}
16\,dx,&0<x\le3,\\
25\,dx,&3<x\le4,\\
33\,dx,&4<x\le6,\\
0,&\text{fora desses intervalos}.
\end{cases}
$$

Sua massa é $(48+25+66)/139=1$. A nota `NATIVE_CARRY_PRIMITIVE_TO_SPECTRAL_BRIDGE_AUDIT` também registra a recuperação dessa medida a partir das linhas do operador primitivo em cortes crescentes. Esses resultados de convergência são evidência numérica da nota; a auditoria exata desta rodada parte das fórmulas dos momentos limite.

No Hilbert $L^2(\nu_*)$, a fonte constante $1$ e o gerador de multiplicação

$$
(Yf)(x)=(1+\log x)f(x)
$$

fornecem um kernel resolvente positivo. Com $y=1+\log x$ e a convenção de produto interno antilinear na primeira entrada,

$$
k(\lambda,\mu)
=\int\frac{d\nu_*(x)}{(\overline\lambda-y)(\mu-y)}.
$$

Essa é uma construção matemática a partir da medida, no domínio do resolvente. Não é ainda a identidade do kernel nativo de altura.

O posto um de $P_*$ **seleciona uma fonte**. Sua dilatação por $Y$ atua em um espaço infinito, com suporte contínuo; portanto não limita a órbita a dimensão um. Se, porém, usarmos somente a matriz de seis câmeras como operador final, a dimensão finita continua insuficiente para independência em todas as ordens. A passagem à dilatação ou a um atlas crescente deve fazer parte da construção.

## 5. Como isso se relaciona com o “1” do kernel anterior

No [kernel Hilbert R/B anterior](c3-projective-hilbert-readout-kernel.md), o limite inferior $1$ vinha da coordenada inicial $x_{q,t}(0)=1$. Aqui os cinco autovalores $1$ vêm da variância universal dos modos puros na coordenada logarítmica centrada. São objetos distintos, com definições e espaços distintos.

A pista acrescenta uma maneira derivada da geometria de passar da energia total para uma **energia de retorno**. Não demonstra que apagar a primeira coordenada do estado anterior produz essa energia.

Para fechar a costura ainda precisamos conectar o readout dessa realização, com os fatores e bordos apropriados, a

$$
a(t)=-\frac{F'(t)}{2F(t)},
\qquad
K(x,z)=\frac{a(z)-a(x)}{z-x}.
$$

Na [interface da rodada anterior](../CarrySelfAdjointOperator/C3ProjectiveHilbertReadoutKernel.lean), isso pode ser feito construindo $S,u$ com órbita independente e provando que a válvula dos seus momentos coincide com `completedProjectiveStateReciprocalMass`. Os parâmetros do resolvente, a coordenada $1+\log(n/M)$ e a altura nativa continuam explícitos até demonstrar o transporte.

O arquivo `Camera/ModalEnergy.lean` já define a amplitude mista com o produto do fator binário e do fator da câmera 3, multiplicando `nativeScalar`. Sua igualdade de fatorização é imediata da definição. Ela é uma referência para os fatores corretos; por si só não prova que a scalarização $P_*$ deste POVM realize o Gram nativo.

## 6. Cuidados concretos ao reutilizar as notas ampliadas

Na nota `COMPOSITE_NONUNIVERSAL_DEFECT_FACTORIZATION_GATE`, a fatorização está correta. Duas passagens exigem manter as coordenadas e transpostas:

- O fator que anula os eixos universais crus é $GT-H$. No pacote de seis câmeras, $(TG-H)e_3=6\log2\,e_6\ne0$, enquanto $(GT-H)e_3=0$. Após whitening, os eixos também são transportados por $G^{1/2}$.
- Se $V=F_{\rm cam}G^{-1/2}$ é a isometria whitened, a identidade da nota usa o slope transportado $\widetilde T=G^{1/2}TG^{-1/2}$: $YV=V\widetilde T+\mathcal UV$. A identidade projetada $(I-VV^*)YV=(I-VV^*)\mathcal UV$ permanece igual. Não é necessário eliminar essa rota por causa da troca de coordenadas.

O documento `FULL_ATLAS_NONUNIVERSAL_SOFT_EDGE_THEOREM` propõe uma extensão infinita. Seu alcance não foi auditado integralmente nesta rodada. A nova fatorização Lean vale para cada família finita com Gram positivo definido; não afirma que o posto continue um, nem fornece por si estimativas uniformes quando o atlas cresce.

## 7. Evidência e próximo passo

O módulo e as 14 etapas da auditoria completa passaram com `--wfail`; as sete declarações usam somente `propext`, `Classical.choice` e `Quot.sound`. As 14 verificações simbólicas também passaram. O módulo foi integrado ao import geral e a `KernelConstructionAudit`. A [evidência reproduzível](../research/camera-return-defect-2026-09-05/verification.json) reúne os sete teoremas, axiomas transitivos, hashes e o resultado da auditoria completa. A [auditoria simbólica](../research/camera-return-defect-2026-09-05/exact_camera_return_audit.py) verifica separadamente as fórmulas racionais, o defeito de posto um, as transpostas e a medida por intervalos.

A próxima tentativa pode partir do raio $p_*$ e da sua dilatação de retorno. A obrigação passa a ser acompanhar esse readout até a característica completada e seus momentos, preservando a mesma energia e os bordos. Essa escolha de fonte tem origem geométrica concreta; a igualdade final permanece uma prova a realizar.

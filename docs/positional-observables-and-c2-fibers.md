# Observáveis posicionais e transporte nas fibras C2

Base: `5b117ff4ca65247dbc5b26dc8636332cfb6f20ce`.
Estudo de 2026-09-09. Dependency pins e toolchain preservados.

## Resultado

A matriz `finiteDepthShift` amostra o próximo estágio de ambas as trajetórias
abaixo. Não é necessário identificar um par de coordenadas com `Fin N`.
A identidade é genérica para qualquer sequência; a interpretação geométrica
vem da trajetória que se amostra.

| Trajetória | Dado fixo | Variação |
| --- | --- | --- |
| Carta posicional | base e número n | quociente e resíduo na profundidade k |
| Fibra C2 | core m e offset ε | número 2^k m + ε |

## 1. Próxima carta e bordo

`FinitePositionalObservableShift.lean` define `finitePositionalObservable`
usando diretamente `positionalDepthCoordinates`, do módulo anterior.

Para qualquer sequência real f, em um prefixo de N+1 amostras:

$$
(S_{N+1}f)_i+\mathbf1_{i=N}f(N+1)=f(i+1).
$$

É `finiteDepthShift_sample_add_boundary`. Para
f(k)=F(positionalDepthCoordinates b k n), o resultado transporta para
`positionalDepthRefinement` no interior. Para a diferença ponderada:

$$
(\nabla_{q,N+1}v_F)_i+
q^{-1}\mathbf1_{i=N}F(X_{N+1})
=q^{-1}F(X_{i+1})-F(X_i).
$$

Teorema: `finitePositionalObservable_difference_add_boundary`.
A omissão da última amostra fica explícita. Esta identidade não pressupõe
positividade ou escolha da métrica.

## 2. Limite dos observáveis de um número fixo

Se b>1 e k≥n, então n<b^k e X_k=(0,n).
`positionalObservable_stable` prova F(X_k)=F(0,n).
Consequentemente, `no_positionalObservable_eq_depth` prova:

```lean
¬ ∃ F : ℕ × ℕ → ℝ,
    ∀ k, F (positionalDepthCoordinates b k n) = (k : ℝ)
```

A restrição é exatamente a um único n fixo e um observável que depende
apenas do par. Não exclui observáveis de (k,par), uma família de n, pesos
explícitos em profundidade, ou uma trajetória de números crescentes.
A diferença ponderada no trecho estável é (q⁻¹-1)F(0,n); só a diferença
ordinária, q=1, se anula automaticamente.

## 3. Fibra C2 e logaritmo do centro

`C2FiberDepthLogTransport.lean` define a coordenada real
x_k=2^k m+ε. Para ε=±1 ela é identificada com os dois pontos naturais das
pernas; a identificação da subtração natural exige m>0. A lei afim e a
álgebra logarítmica valem mais geralmente para qualquer offset real.
Na interpretação de incidências C2 da nota, usam-se core ímpar positivo,
ε=±1 e profundidade k≥2.

$$
x_{k+1}=2x_k-ε,\qquad x_k-ε=2^km.
$$

Para m>0:

$$
\log(x_k-ε)=k\log2+\log m.
$$

Definindo L como a matriz diagonal dessa leitura centrada, prova-se:

$$
L=L_{\rm depth}+\log(m)I,
\qquad [\nabla_{q,N},L]
=\texttt{finiteNativeDepthCommutator}(2,q,N).
$$

Teorema principal: `finiteC2FiberCenteredLog_commutator`.
O termo constante do core comuta e cancela. A definição original de
`finiteNativeDepthCommutator` é reutilizada, sem outro operador espectral.

O vínculo aos modos já existentes é:

$$
\log(x_k-ε)\,\operatorname{criticalAmplitude}(2,k)
=\log2\,E_1(k)+\log m\,E_0(k).
$$

Teorema: `c2Fiber_centeredLog_amplitude_eq_green_and_seed`.
Reutiliza `newtonJet_zero_eq_criticalAmplitude`; a identificação de E1 com
Green continua sendo `newtonJet_one_eq_carryGreenKernel`, já provada.
O core contribui pelo modo zero: não deve ser apagado.

## 4. Primeiro termo que impede trocar centro por perna

Para x_k≠0 e m>0:

$$
\log x_k-\log(x_k-ε)
=d_k:=\log\left(1+\frac{ε}{2^k m}\right).
$$

Para dois pontos consecutivos não nulos:

$$
\log x_{k+1}-\log x_k=\log2+d_{k+1}-d_k.
$$

Teoremas `c2FiberPoint_log_center_defect` e
`c2FiberPoint_log_increment_defect`. A correção não é apenas uma
possibilidade: no core 1, perna +1, profundidades 2 e 3,
`c2FiberPoint_right_log_increment_lt` prova

$$
\log9-\log5<\log2.
$$

Assim, o comutador centrado está identificado, mas a substituição pela
leitura literal da perna exige transportar a diagonal d e seu comutador.
Isso não é um no-go para o kernel completado nem identifica o defeito
Gamma–Wronskiano.

## 5. Peça antiga que já foi corrigida no pin

`CPFormal/Carry/C2OddCorePushforward.lean` já define
`oddCoreMinusDepth`, `oddCorePlusDepth` e `oddCoreTruncatedMass`.
Para 0<m≤M, `oddCoreTruncatedMass_richardson_exact` prova

$$
2a_{8M}(m)-a_{4M}(m)=1.
$$

A nota antiga não precisa fornecer uma nova fórmula de cutoff: a
formalização existente conserva os dois limites de perna separadamente.

## Próxima obrigação matemática

Agora existe uma realização do comutador de profundidade por leitura do
centro de uma fibra e um termo exato para trocar essa leitura pela perna.
Falta transportar esses dados completos para a câmera literal e demonstrar
as igualdades de produtos internos com os momentos nativos. O shift de
amostras sozinho não determina o Hankel, sua positividade ou o Jacobi.

O fator de massa 1/b descreve a contagem das extensões na projeção entre
janelas residuais uniformes; uma trajetória de n fixo seleciona só uma
extensão. Nenhuma medida de alturas é deduzida dessa contagem neste estudo.
A fonte formal já consumida é `CarryGeometry.Probability`: os teoremas
`residueClassEvent_probability` e `incrementCarryEvent_probability`
identificam a probabilidade uniforme com `carryMass`. A contagem das
janelas vem de `card_admissibleDigitStrings` e
`eval_bijects_admissibleDigitStrings_and_residues`.

## Verificação

`PositionalFiberShiftAudit.lean` imprime os axiomas de todos os teoremas
novos. O workflow a executar é `bash scripts/audit.sh`, além de
`git diff --check`. Os resultados efetivos são registrados no arquivo
`positional-fiber-shift-validation.md` ao término.

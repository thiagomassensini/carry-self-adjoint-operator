# Cumulantes corrigidos e Hankel

A base para aplicar os módulos é o commit
`1d058c1e008401e56d47246859869a69726bb9f3` do PR #127 do CSA.
Os arquivos Lean ficam em `CarrySelfAdjointOperator/`.
[PR #127](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/127)

- `C2MellinAllOrderMajorant.lean` demonstra a envolvente integrável
  $2\cdot 8^r r!\,e^{-x}(x^{-3/4}+x^{-1/4})$ para o integrando de
  ordem $r$ em $3/8<s<5/8$.
- `C2ClockAllOrderDerivative.lean` justifica todas as diferenciações
  sob a integral do relógio. Define a correção $D$ e mostra que, dado
  o produto local $F=D\,I$ e a regularidade indicada, o jato do
  logaritmo é a soma dos dois jatos.
- `C2ClockNativeDensityBridge.lean` identifica a densidade comum e a
  sua dilatação com a densidade de pernas do PR #127.
- `C2CorrectedCumulantHankel.lean` identifica o jato logarítmico na
  coordenada par com o momento canônico, transporta a positividade
  pela congruência de sinais e calcula os menores consecutivos
  $2\times2$ sob a identidade ponto a ponto. O menor inicial
  reaproveita o certificado theta do CSA.
- `C2ClockQuadraticJet.lean` transporta os coeficientes da série
  logarítmica por $u=-t^2$. A substituição insere zeros nos graus
  ímpares e fornece o sinal e o fatorial dos cumulantes pares.
- `C2ClockCanonicalCumulants.lean` cancela $1+2^{-s}$ no fator
  original da câmera, aplica o completamento e liga o produto
  local ao jato em $u=-t^2$. Instancia a equivalência de Hankel
  com os cumulantes da própria fonte.

O teorema `c2ClockCorrectedCumulant_eq_canonical` estabelece
$C_{2n+2}=2(-1)^n(2n+1)!\,h_n$ para todo $n$. A prova usa a
carta nativa com cauda exata, o fator comum $1-2^{1-s}$, a
correção arquimediana e a ponte par existente no CSA. Nenhuma
entrada espectral de zeros ou hipótese de sinal é necessária.
A positividade canônica em toda ordem segue como obrigação
após a identificação dos jatos.

O certificado theta para o menor inicial fornece uma comparação
independente. `c2ClockCorrectedCumulant_second_minor_pos`
transfere o sinal já certificado para os cumulantes da fonte.
[Certificado theta](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/1d058c1e008401e56d47246859869a69726bb9f3/CarrySelfAdjointOperator/CompletedNativeSixthOrderThetaPositivity.lean#L79)

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

O passo que fecha a identificação dos dois lados no Lean é ligar
o produto na coordenada de Dirichlet ao jato par na coordenada de
altura. Ele usa a carta nativa com cauda exata, a divisão pelo
fator comum $1-2^{1-s}$, a correção arquimediana e a substituição
$s=\tfrac12+iz$, $u=z^2$. Essa ligação completa ainda não é um
teorema destes módulos. A positividade canônica em toda ordem
continua sendo uma obrigação separada, mesmo depois da igualdade
dos jatos.

O certificado theta para o menor inicial fornece uma comparação
independente. A álgebra dos cumulantes por si só fornece a
desigualdade equivalente, sem uma nova prova do seu sinal.
[Certificado theta](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/1d058c1e008401e56d47246859869a69726bb9f3/CarrySelfAdjointOperator/CompletedNativeSixthOrderThetaPositivity.lean#L79)

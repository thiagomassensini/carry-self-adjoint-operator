# Checkpoint — geometria nativa até o operador de alturas

## O que foi fechado

O caminho formalizado agora pode ser lido na direção causal da construção:

`C2/carry -> bracket e TFVD -> cauda exata -> válvula/Green -> resposta causal + retorno de bordo -> energia nativa -> lei de bordo/shift -> Jacobi finita -> operador de alturas simétrico`.

O novo módulo `CarrySelfAdjointOperator/NaturalNativeGeometryOperatorAudit.lean`
adiciona a composição
`canonicalC2Geometry_native_sameGeometry_energy_to_height_operator_of_radialHerglotz`.
Ela começa na positividade Herglotz/Pick da válvula radial completada e na
não-degenerescência de incidência, constrói a dominância quiral estrita e
invoca o capstone fonte-direção.  A hipótese de entrada não é Gram, Cholesky,
Jacobi nem espectro ajustado.

## O que o capstone expõe antes do operador

- o readout de bracket/TFVD;
- a identidade exata de cauda sobre todos os centros;
- a soma resposta Green + retorno de bordo, que recompõe o estado gradiente;
- a identidade de energia como quadrado adjunto do readout nativo;
- a equação polarizada de coeficientes e a lei de primeira coluna/shift;
- somente depois disso, a seção de Jacobi e `nativeGeometryFiniteHeightOperator`.

## Gate que permanece honesto

O módulo não afirma que a positividade Herglotz de todas as ordens já foi
provada pela geometria. Ele identifica precisamente esse enunciado como o
gate material restante, junto da não-degenerescência nativa já isolada. A
equivalência formal usada é:

`radial chiral multiplier contractive <-> radial Herglotz/Pick positive`.

O resultado de duas pontas (`N = 2`) continua sendo apenas validação de baixa
ordem; não é promovido a positividade em todas as ordens.

## No-go preservado

O carrier bruto de câmera/projetivo e o jet Taylor complexo não são usados:
há resíduos exatos de ordem zero/primeira coluna e de translação. O carrier
correto conserva resposta causal e retorno de bordo no espaço Hilbert; a
normalização final é aplicada ao readout completado, não ao Gram bruto das
linhas da câmera.

## Checkpoint adicional — rotação Green antes de Hankel

Foi compilado no Lean o seam operatorial que faltava para tornar explícita a
interpretação geométrica da autoadjunção:

- `inner_canonicalCompletedC3RadialSymplecticRotation_left` prova que a
  rotação radial nativa é skew-adjunta;
- `inner_canonicalCompletedC3GlobalGreenOperator_left` prova o mesmo para o
  carrier global, que mantém separados o bloco radial resposta/retorno e o
  bloco archimedean/chart;
- `canonicalC2Geometry_native_globalGreenOperator_quarterTurn` prova
  simultaneamente a simetria da rotação `-iT` no produto interno e
  `(-iT)^2 = I`.

Portanto a primeira autoadjunção que nasce da geometria é a involução
Hermitiana obtida da rotação simplética do Green. Ela aparece antes de
momentos, Hankel, Cholesky ou Jacobi. O operador de alturas finito continua
sendo a compressão positiva downstream dessa cadeia, não essa rotação
skew-adjunta em si.

Também foi compilado o capstone
`canonicalC2Geometry_native_green_operator_to_height`: sob o transporte
material corrigido da primeira coluna e o transporte injetivo de incidência,
ele expõe juntos a lei de coeficientes Green polarizados, a
`HasPolarizedCoefficientVectorEquation` do jet material e a existência da
seção de alturas finita simétrica.

## Fronteira exata após este avanço

Não falta uma igualdade algébrica entre o Green e o operador. Essa parte agora
é exata no carrier operatorial. O único input material não descarregado é
`HasCorrectedNativeChiralBoundaryTransport` (equivalentemente,
`HasSameEdgeGreenToClockBoundaryTransport`): a igualdade vetor/coeficiente da
primeira coluna do atlas de relógio com o readout Green corrigido. A identidade
de cauda já está fechada e não é a obstrução. O transporte de incidência já
fornece a não-degenerescência; o gate restante é calibrar essa primeira coluna
sem substituir o carrier por um proxy positivo.

Verificação: módulo isolado e `lake build` completo passaram; os três novos
teoremas reportam apenas `[propext, Classical.choice, Quot.sound]`.

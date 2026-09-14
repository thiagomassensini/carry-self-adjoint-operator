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

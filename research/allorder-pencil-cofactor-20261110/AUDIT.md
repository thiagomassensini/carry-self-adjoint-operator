# Auditoria — all-order pencil/cofactor

## Proveniência e limites

- Os momentos são os `canonicalCompletedNativeLogDerivativeMoment` já definidos na cadeia da fonte. Não foram redefinidos por zeros, alturas ou modos espectrais.
- O `nativeSourceCofactorThetaPolynomial_integral_bordered` existente é uma identidade sem hipótese de invertibilidade ou positividade. Usa adjugata/determinante, e identifica a integral com um escalar bordeado.
- `nativeSourceCofactorSign_iff_stieltjes` identifica um gate de sinal all-order com a positividade de Stieltjes. É uma equivalência, não uma derivação da desigualdade de fonte.
- `nativeSchurEuler_even_balance` e `nativeSchurEuler_odd_balance` requerem que o prefixo anterior seja `IsUnit`. O balanço ímpar retém um quadrado não negativo, mas também retém uma integral assinada.
- `nativeSchurEuler_odd_pos_iff_mass_balance` é condicional à mesma invertibilidade e reduz o sinal do pivô a uma desigualdade estrita entre massas. A dominância das massas não está provada.
- `NativeSourceSchurThetaMasses.lean` define massas positiva e negativa como integrais de partes positiva/negativa e prova que a massa negativa é estritamente positiva em toda ordem ímpar. Logo não se pode substituir a integral assinada por uma alegação de não negatividade pontual.
- `NativeSourceThetaGreenTransport.lean` mantém explicitamente os termos de fronteira na integração de Green; depois mostra que os traços centrais dos polinômios Schur específicos se anulam. A transferência não estabelece densidade não negativa.
- `GreenWronskianHankelBridge.lean` prova positividade das Hankel sob uma representação de Gram de um único kernel de Green e independência linear dos jets (para positividade estrita). Esse módulo não constrói tal representação para os momentos nativos completados; usá-la como se já estivesse construída seria hipótese analítica adicional.

## Categorias de resultado

| Categoria | Estado atual |
|---|---|
| Identidade algébrica provada no código existente | Cofatores, escalar bordeado e integral cofactor theta (`nativeSourceCofactorThetaPolynomial_integral_bordered`). |
| Identidade algébrica provada nesta branch | `nativeSourceHankelPencilPolynomial_eq_cofactor`: `det(XG-K)` igual ao polinômio da direção de cofatores para todo `s,n`, sem hipótese de inversibilidade ou sinal. A transformação triangular tem determinante 1; a prova é division-free. |
| Identidade algébrica provada nesta branch | `nativeSourceHankelCriticalVector_mul` e `nativeSourceHankelCriticalVector_energy`: a janela seguinte aplicada ao vetor crítico dá `(0,…,0,τ_{s,n+1})`, com energia `τ_{s,n}τ_{s,n+1}` para todo `s,n`. |
| Identidade algébrica provada nesta branch | `nativeSourceCofactorThetaPolynomial_integral_eq_prefixDet_mul_succ`: a integral original é `c₀τ_{s,n}τ_{s,n+1}`, sem hipótese de sinal. |
| Teorema condicional novo | `nativeSourceCofactorThetaPolynomial_integral_pos_iff_nextPrefixDet_pos` requer explicitamente `0<c₀` e `0<τ_{s,n}`; não prova `0<I_{s,n}`. |
| Teorema Lean existente com hipótese explícita | Critério Schur de extensão positiva e balanços Euler para prefixos invertíveis. |
| Teorema condicional | Equivalência entre o sinal do pivô ímpar e a dominância das massas, sob `IsUnit`. |
| Hipótese analítica da fonte | Uma desigualdade que domine a massa theta negativa pela massa positiva (e pelo quadrado ímpar sobrevivente). |
| Teste numérico/simbólico | Não usado como fundamento de resultado universal nesta branch. As notas de pesquisa mencionam testes finitos, que não substituem prova para todo `n`. |
| Conjectura/obrigação aberta | As duas dominâncias Euler/theta para todo grau, suficientes para as duas torres Hankel. |

## Riscos de circularidade a evitar

1. Não provar positividade de `nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial s n)` assumindo `CanonicalCompletedNativeStieltjesPositivity`; a equivalência existente já mostra que isso contém o gate desejado.
2. Não obter `sourceMomentMatrix` positiva a partir de um Gram positivo cuja representação para a fonte completada ainda não foi construída.
3. Não descartar a parcela negativa da integral Green/Euler. Os arquivos de massas e transporte documentam contribuições negativas reais.
4. Não usar as identidades do pencil, energia ou Toda para inferir sinal sem hipóteses explícitas; essas identidades são division-free e algébricas.
5. Não interpretar `IsUnit`/`PosDef` dos balanços condicionais como resultado all-order já estabelecido.

## Estado do ambiente

- Repositório correto e branch nova confirmados; alterações já existentes no checkout principal ficaram fora da worktree.
- Lean fixado em `leanprover/lean4:v4.32.0`; Lake e todas as revisões do manifest foram lidos.
- Uma primeira resolução foi interrompida durante a obtenção de pacotes. Os clones resultantes foram preservados; `.lake/packages` da worktree foi apontado para a cache existente do checkout principal, com as revisões do manifest mantidas. `lake env lean --version` passou depois disso.
- O build da dependência `NativeThetaCofactorMargin` no checkout isolado começou a recompilar um grafo amplo com certificados theta (interrompido em 9300/9844 tarefas, sem erro relatado). Para compilar o módulo novo, foi usado `lake env lean` do checkout principal com o arquivo de fonte na worktree; o `.olean` da margem corresponde ao último commit sem alteração do respetivo fonte. Resultado: exit code 0, sem warnings.
- `nativeSourceHankelPencilPolynomial_eq_cofactor` foi compilado no módulo focado para todos os `s,n`; seu enunciado não assume `IsUnit`, `PosDef` ou qualquer sinal. O caso `n=0` está incluído no teorema geral.
- `nativeSourcePrefixDet_succ_eq_borderedScalar`, `nativeSourceHankelCriticalVector_mul` e `nativeSourceHankelCriticalVector_energy` também compilam para todo `s,n`, sem inversa, positividade ou condição de posto.
- `NativeHankelPencilThetaBridge.lean` compila contra o módulo do checkpoint 2; a identidade integral usa o teorema bordeado original e a equivalência de sinal permanece condicional. O teorema `nativeThetaCofactorSign_iff_stieltjes` não foi reescrito.
- A compilação focada terminou com exit code 0. Lean imprimiu apenas uma sugestão de reescrita por `ring_nf`; isso não foi erro nem lacuna. Não foi alegada compilação do grafo completo de Lake, cujo build anterior foi interrompido por custo.
- Os dois documentos de pesquisa pedidos foram lidos da branch remota `research/sigma-pade-dimension-depth-20261104` do repositório `momentos`. Ambos dizem explicitamente que a síntese é algébrica/em papel e não anuncia novo build Lean nem prova de dominância all-order.

# Checkpoint: TFVD/Parseval → projetivo-quiral/Cauchy–Pick

Data: 2026-11-17. Repositório: carry-self-adjoint-operator.
Branch isolada: task/projective-chiral-parseval-20261117.
Base: origin/main f1df607.

## Objetivo e delimitação

A pergunta é como transportar o pareamento COMPLETO da fonte física nativa,
incluindo seed/bordo, Green, retorno e cruzamentos, para a forma projetivo-quiral
que já reproduz o kernel polarizado de diferenças divididas (dslope).

A mudança escalar de coordenadas da válvula, a igualdade de massas formais,
uma leitura linear dos jets X_n e a isometria Parseval do Gram bruto NÃO
identificam por si a forma física com o kernel canônico.

Este checkpoint fornece uma interface tipada de confronto, sem construir
um mapa faltante ou pressupor momentos/positividade.

## Teoremas acrescentados

Arquivo: CarrySelfAdjointOperator/ProjectiveChiralParsevalSourceSewing.lean

O carrier de entrada é literalmente CPFormal.Analytic.Cp.CarryVerticalL2,
não a família comprimida X_n de dimensão 24.

1. sourceChiralParsevalPairing_eq_source:
   P é a análise Parseval já formalizada, e para pares (v+,v-), (w+,w-),
   B(Pv,Pw) = ( <v+,w+> - <v-,w-> ) / 2.
   É identidade de forma assinada, não isometria que transforme diferença
   de energias em norma positiva.

2. sourceChiralParsevalDefectMatrix_eq_source:
   o defeito matricial no Green-frame é exatamente Gram(v+) - Gram(v-),
   no carrier original, com todos os produtos internos complexos.

3. sourceChiralParsevalDefectMatrix_posSemidef_iff:
   a positividade deste defeito é EQUIVALENTE à desigualdade
      ||sum c_i v-_i|| <= ||sum c_i v+_i||
   para TODA combinação complexa finita. Nenhuma norma ponto a ponto basta.

4. sourceProjectiveChiralMetricSewingDefect_eq_mismatches:
   para a grade radial regular (k,N), sejam P+ e P- os estados canônicos
   projetivo-quirais Cauchy e multiplicador com amplitude exata.
   D_sew(i,j) = 1/2 * (D_plus(i,j) - D_minus(i,j)),
   onde D_plus = <v+_i,v+_j> - <P+_i,P+_j>
         D_minus = <v-_i,v-_j> - <P-_i,P-_j>.
   A definição do alvo usa o dslope nativo; a prova abre a forma quiral
   JÁ PROVADA e preserva ambas as matrizes de Gram com seus cruzamentos.

5. sourceProjectiveChiralMetricSewingDefect_zero_iff:
   a costura métrica completa equivale à compensação D_plus=D_minus
   em TODAS as entradas ordenadas. Não exige, nem prova, que as parcelas
   separadas se anulem.

6. sourceProjectiveChiralDslope_eq_half_sourceDefect:
   sob costura entrywise, a matriz canônica dslope é metade do defeito
   de Gram da fonte após Parseval.

7. sourceProjectiveChiralDslope_posSemidef_of_sewing_and_contractivity:
   costura exata + dominação física para todas as combinações =>
   matriz dslope canônica positiva semidefinida.

Os resultados são lemmas de transporte/costura condicionais (onde indicado).
Nenhum fornece a instância física faltante para v+/v-, nem estabelece
positividade nativa em todas as ordens ou não degenerescência.

## Proveniência importante

- BR2GreenFrameDslopeLimitBridge.lean:
  canonicalCompletedGreenFrameParsevalAnalysis_inner (isometria existente).
  O teorema de igualdade dslope no frame tem uma hipótese de kernel explícita.
- CompletedNativeProjectiveChiralCarrier.lean:
  canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_eq_dslope.
- CompletedNativeRadialChiralMultiplier.lean:
  gram_sub_gram_posSemidef_iff_synthesis_norm_le e equivalência Pick/contraction.
- CompletedNativeProjectiveChiralForwardDifference.lean:
  os limites dos jets assinados formam as duas Hankels nativas.
- GoN: CarryMaterialTfvdProjectiveTransport.lean e
  CarryMaterialProjectiveReturnGreen.lean:
  já conservam fonte, bordos, GG/GR/RG/RR e retorno global físico,
  mas seus carriers não estão identificados com os v+/v- deste módulo.

## Experimento numérico auxiliar

Arquivo: research/projective-chiral-parseval-20261117/diagnostic.py
Saída:  research/projective-chiral-parseval-20261117/numerical-results.json

Com F(z)=A(z) zeta(1/2+i z), q(z)=(-F'(z)-iF(z))/(-F'(z)+iF(z)),
z_i=i(i+1)/(k+1) (i é índice), foi formada a matriz

  D_ij = (k+1)/(i+j+2) * (1 - conjugate(q(z_i))*q(z_j)).

A congruência K_ij = conjugate(a_i)*a_j*D_ij/2 foi recalculada
independentemente por diferenças divididas de -F'/(2F).
Todos os autovalores das seções avaliadas foram numericamente positivos.

Precisão: 130 dígitos (mpmath). Menores autovalores:
- k=12,  N=3:   7.7631182762942384e-12
- k=32,  N=4:   5.7488509291329655e-19
- k=64,  N=6:   1.3652307078410803e-32
- k=80,  N=8:   1.6670278093765810e-45
- k=100, N=10:  7.6693422613490907e-59
Erros máximos da congruência <4e-129 nesses casos.

Os cálculos NÃO são certificados intervalares e não inferem um quantificador
de positividade para N arbitrário nem constroem fonte física.

## Validação Lean

lake env lean -DwarningAsError=true \
  CarrySelfAdjointOperator/ProjectiveChiralParsevalSourceSewing.lean

PASS. #print axioms nos sete lemas: apenas propext, Classical.choice,
Quot.sound. Sem sorry/admit/axiomas novos.

## Próxima obrigação de fato

Escolher e construir, a partir do estado físico nativo GoN completo,
dois canais v+/v- no carrier TFVD (ou uma realização compatível com
Mapas lineares/isométricos já presentes). É preciso provar para todas as
entradas de uma grade radial finita:

  sourceProjectiveChiralPositiveMismatch(k,N,v+,i,j)
    =
  sourceProjectiveChiralNegativeMismatch(k,N,v-,i,j).

A igualdade deve surgir dos lemas fonte Green/TFVD/completion/return,
não ser posta como premissa de um construtor concreto. Separadamente,
demonstrar a desigualdade de síntese para todas as combinações finitas,
sem usá-la como hipótese implícita da construção.

Só depois a rota chega à positividade das duas Hankels via os teoremas
de limite dos jets, e a positividade estrita exige não degenerescência.

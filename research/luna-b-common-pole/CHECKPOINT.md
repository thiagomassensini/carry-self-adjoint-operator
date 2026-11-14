# Luna B checkpoint

- Fase: B1, B2 e B3 concluídas; validação final passou; PR draft a abrir.
- Repositório/branch: `carry-self-adjoint-operator`, `agent/luna-b-common-pole-20261114`.
- Worktree isolada: `/home/thlinux/worktrees/csa-common-pole-20261114`.
- SHA-base usado: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532` (`origin/main`).
- Dependências/pins inalterados; sem `AGENTS.md` na raiz/árvore versionada consultada.
- B1 commit/push: `380061f3b887b656ea8d9d324710a37794b9177f`.
- B2 commit/push: `460843c8e69255623cba97cab976afc98a9ee770`.
- B3 commit/push: `5f1eaf374793c072ebcc26fd1b0c9d488383fe49`.
- B1 prova matriz geométrica rank-one e forma quadrática para todos `α,ρ,s,n,x`; sequência C2 `p(j)=-2(-4)^j`; canal `p` cancela com `-p`.
- B2 prova regras genéricas de resposta produto/quociente, `R_(s-1)` e parte ímpar, diferença dividida com identidade multiplicada válida na diagonal, série racional formal única e seus coeficientes ímpares `p(j)`.
- B3 usa `factor 2=c2Factor` e o bracket completo original; prova `F=A B/Q`, `F=a B/q` como germes críticos, cancelamento de canais e igualdade de todos os jets.
- Normalizações: `-F'/F=2R_F`; teorema existente reutilizado dá `nativeSourceOddBoundaryCoefficient j=2*primeDepthGeometricMoment j`.
- Validação: `scripts/validate-luna-b-common-pole.py` compilou 5 módulos com warnings como erros, canários, auditoria transitiva e `git diff --check`; 26 declarações auditadas dependem só de `propext`, `Classical.choice`, `Quot.sound`.
- Busca por `sorry`, `admit` e declarações `axiom` nos módulos novos: vazia.
- Nenhum sinal/positividade foi afirmado; nenhum zero espectral/representação é usado no cross identity.
- O prolongamento removível de `q` em `s=1` não foi formalizado; não é necessário no germe `s=1/2`.
- Próximo passo exato: abrir a PR draft contra `main`, sem merge.

# Validação final

| Comando | Saída | Log |
| --- | --- | --- |
| `/usr/bin/python3 /home/thlinux/carry-self-adjoint-operator/research/critical-branch-native-audit/check_sources.py` | 0 | `evidence/source-check.log.gz` |
| `lake build --wfail CarrySelfAdjointOperator.CriticalBranchNativeObstructions CarrySelfAdjointOperator.CriticalBranchNativeAudit` | 0 | `evidence/focused.log.gz` |
| `lake build --wfail` | 0 | `evidence/root.log.gz` |
| `lake build --wfail CarrySelfAdjointOperator.Audit` | 0 | `evidence/audit-root.log.gz` |
| `/usr/bin/python3 scripts/check_physical_sewing_registry.py` | 0 | `evidence/physical-registry.log.gz` |
| `git diff --check` | 0 | `evidence/diff-check.log.gz` |

Auditoria dedicada: **25 raízes**, fechamento de **7853 declarações** por tipos/corpos. Apenas `propext`, `Classical.choice`, `Quot.sound`.

O scanner `scripts/static_audit.sh` **não passou** (saída 1): os únicos três matches são comentários preexistentes e inalterados da base. `check_static_baseline.py` verificou cada linha contra `045369f...`; detalhes em `evidence/static-baseline.json` e no log comprimido. O kernel e o scanner do código de prova novo passaram.

Os totais de jobs Lake incluem dependências e replay de cache; não significam compilação limpa integral de cada dependência. Não foi usado um resultado numérico como premissa. `verify_evidence.py` confere os códigos de saída e hashes dos logs.

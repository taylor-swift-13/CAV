# Execution Issues

## Agent Protocol Violation

- Reason: `agent_exited_before_success_or_legal_fail`
- Audit detail: `missing_generated_files:/home/yangfp/CAV/C/CAV/output/verify_20260608_125304_p121_solutions/coq/generated/p121_solutions_proof_manual.v`
- Final result detail: `missing_metrics:/home/yangfp/CAV/C/CAV/output/verify_20260608_125304_p121_solutions/logs/metrics.md`
- Last message: `/home/yangfp/CAV/C/CAV/output/verify_20260608_125304_p121_solutions/logs/agent_last_message_20260608_125304.txt`
- Expected behavior: keep proving/editing until QCP final-check succeeds, external timeout stops the run, or a contract/original C/V spec blocker requires Contract/user decision.

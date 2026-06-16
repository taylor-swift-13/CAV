# Execution Issues

## Agent Protocol Violation

- Reason: `agent_exited_before_success_or_legal_fail`
- Audit detail: `source_integrity_failed:/home/yangfp/CAV/C/CAV/output/verify_20260608_17010424551_p073_smallest_change/logs/source_integrity_gate.log;audit_check_coqc_failed:/home/yangfp/CAV/C/CAV/output/verify_20260608_17010424551_p073_smallest_change/logs/audit_check_coqc.log`
- Final result detail: `missing_metrics:/home/yangfp/CAV/C/CAV/output/verify_20260608_17010424551_p073_smallest_change/logs/metrics.md`
- Last message: `/home/yangfp/CAV/C/CAV/output/verify_20260608_17010424551_p073_smallest_change/logs/agent_last_message_20260608_170104.txt`
- Expected behavior: keep proving/editing until QCP final-check succeeds, external timeout stops the run, or a contract-program mismatch blocker requires Contract/user decision.

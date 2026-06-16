# Execution Issues

## Agent Protocol Violation

- Reason: `agent_exited_before_success_or_legal_fail`
- Audit detail: `source_integrity_failed:/home/yangfp/CAV/C/CAV/output/verify_20260608_130522_p100_make_a_pile/logs/source_integrity_gate.log;missing_generated_files:/home/yangfp/CAV/C/CAV/output/verify_20260608_130522_p100_make_a_pile/coq/generated/p100_make_a_pile_proof_manual.v`
- Final result detail: `missing_metrics:/home/yangfp/CAV/C/CAV/output/verify_20260608_130522_p100_make_a_pile/logs/metrics.md`
- Last message: `/home/yangfp/CAV/C/CAV/output/verify_20260608_130522_p100_make_a_pile/logs/agent_last_message_20260608_130522.txt`
- Expected behavior: keep proving/editing until QCP final-check succeeds, external timeout stops the run, or a contract/original C/V spec blocker requires Contract/user decision.

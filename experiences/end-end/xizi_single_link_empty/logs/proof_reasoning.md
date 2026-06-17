# Proof Reasoning

## Audit Result

The final QCP audit was run with:

```bash
bash SeparationLogic/examples/CAV/verify_20260614_hil_xizi_single_link_empty/run_audit.sh
```

The audit replay passed:

- source integrity
- `linux-binary/symexec`
- `coqc examples/CAV/verify_20260614_hil_xizi_single_link_empty/deps/xizi_single_link_lib.v`
- `coqc .../xizi_single_link_empty_goal.v`
- `coqc .../xizi_single_link_empty_proof_auto.v`
- `coqc .../xizi_single_link_empty_proof_manual.v`
- `coqc .../xizi_single_link_empty_goal_check.v`

`xizi_single_link_empty_proof_manual.v` contains only the standard generated header and no theorem obligations. This is expected for this straight-line read-only function: generated VCs are safety/return obligations handled by the QCP auto proof, and `goal_check.v` validates the full replay.

No manual proof edits were made, so experience retrieval was not required before tactic work. The reusable lessons from this run were recorded under:

- `experiences/general/CONTRACT/9/xizi-intrusive-sll-closed-pointer-model.md`
- `experiences/general/SYMEXEC/9/xizi-qcp-header-no-preprocessor.md`
- `experiences/general/COMPILE/1/custom-linked-list-strategy-artifacts.md`


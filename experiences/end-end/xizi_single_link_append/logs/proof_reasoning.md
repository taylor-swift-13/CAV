# Proof Reasoning

Generated obligations:

- one scalar safety witness for writing `(void *)0`;
- two entail witnesses for loop initialization and loop preservation;
- one return witness for rebuilding the appended chain.

Key proof ingredients:

- `xizi_sllseg` models the traversed prefix from the head/root to the current tail candidate.
- `xizi_sllseg_len1` and `xizi_sllseg_sllseg` extend the prefix when the loop advances.
- `xizi_sll_zero` turns the loop exit condition `next == 0` into an empty suffix.
- `xizi_sll_len1`, `xizi_sll_cons`, and `xizi_sllseg_sll` rebuild the final chain.

The QCP-generated `proof_auto.v` was replaced by a checked import-only file, and all real function proof obligations are in `proof_manual.v`.

The local strategy file is now backed by case-local Coq files:

- `deps/xizi_single_link_strategy_goal.v`
- `deps/xizi_single_link_strategy_proof.v`

These are compiled by `run_audit.sh`.

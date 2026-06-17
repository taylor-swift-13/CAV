# Proof Reasoning

Generated VCs:

- `xizi_single_link_init_safety_wit_1`: pointer/null constant safety for assigning `0`.
- `xizi_single_link_init_return_wit_1`: after assignment, the head successor cell contains `0` and `xizi_sll 0 nil` holds.

Manual proof strategy:

- keep `proof_auto.v` empty except importing the goal module, so it does not contain generated `Admitted`;
- prove both obligations in `proof_manual.v`;
- for the return witness, instantiate the existential field value with `0`, unfold `xizi_sll 0 nil`, and discharge with `entailer!`.

Audit compiles:

1. `deps/xizi_single_link_lib.v`
2. `xizi_single_link_init_goal.v`
3. `xizi_single_link_init_proof_auto.v`
4. `xizi_single_link_init_proof_manual.v`
5. `xizi_single_link_init_goal_check.v`

The case-local audit also checks that proof files contain no `Admitted`, `admit`, `Abort`, or `Axiom`.

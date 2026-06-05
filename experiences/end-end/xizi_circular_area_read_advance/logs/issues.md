[2026-06-02 19:40:26+08:00] Proof-only verification summary
Phenomenon: The workspace started with `output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v` containing two unresolved lemmas, `proof_of_xizi_circular_area_read_advance_return_wit_1` and `proof_of_xizi_circular_area_read_advance_return_wit_2`, both written as `Admitted`.
Location: `output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v`; compile replay from `QualifiedCProgramming/SeparationLogic`.
Repair action: Replaced the two placeholders with arithmetic proofs only. For `return_wit_1`, normalized `data_length_pre - (area_length_pre - readidx_pre)` to `readidx_pre + data_length_pre - area_length_pre` and applied `Z.rem_unique` using the wrap-around branch facts. For `return_wit_2`, proved the non-wrap remainder bounds with `Z.rem_bound_pos` after establishing `0 <= readidx_pre + data_length_pre`.
Key proof/debug fragments:
`readidx_pre + data_length_pre - area_length_pre = (readidx_pre + data_length_pre) % area_length_pre`
`Set Printing All` showed the generated `%` is `Z.rem`, not `Z.modulo`
`Z.rem_unique : forall a b q r, 0 <= a -> 0 <= r < b -> a = b * q + r -> r = Z.rem a b`
Why this change: In proof-only mode the C/contract/annotations are immutable, so the only valid fix was to align the manual proof with the exact generated arithmetic operator and branch facts.

[2026-06-02 19:40:26+08:00] Compile and integrity result
Phenomenon: After the proof rewrite, the full required compile sequence succeeded for `xizi_circular_area_read_advance_goal.v`, `xizi_circular_area_read_advance_proof_auto.v`, `xizi_circular_area_read_advance_proof_manual.v`, and `xizi_circular_area_read_advance_goal_check.v`.
Location: `output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/`.
Repair action: Cleaned all non-`.v` files under `output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/` after compile, and verified source integrity by comparing `input/xizi_circular_area_read_advance.c`, `annotated/verify_20260602_194026v_xizi_circular_area_read_advance.c`, and `output/verify_20260602_194026v_xizi_circular_area_read_advance/original/xizi_circular_area_read_advance.c`.
Key integrity facts:
`sha256(input) = sha256(annotated) = sha256(original) = 130c69778351cc9fe8db3dc016d3b130958a6d04099affddb139ba9f955562cb`
`cmp` confirmed `input` and `original` match byte-for-byte.
`rg -n '\\b(Admitted|admit|Abort|Axiom)\\b' .../xizi_circular_area_read_advance_proof_manual.v` returned no matches.
Why this change: The verify skill requires both proof completion and a clean workspace replay surface for the runner audit.

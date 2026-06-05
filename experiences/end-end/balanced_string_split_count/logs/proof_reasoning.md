Iteration 1

Phenomenon: after strengthening the invariant and rerunning `symexec`, the remaining manual obligations in [balanced_string_split_count_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/balanced_string_split_count_proof_manual.v:23) are:
- `entail_wit_1`
- `entail_wit_2_1` through `entail_wit_2_4`
- `entail_wit_3`
- `return_wit_1`

Location: generated goals in [balanced_string_split_count_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/balanced_string_split_count_goal.v:400).

Repair plan: keep the witness proofs short and move the list semantics into helper lemmas:
1. prefix-step lemmas for `lr_balance (sublist 0 (i + 1) l)`
2. suffix-step lemmas for `balanced_string_split_count_go balance (sublist i n l)`
3. an exit lemma showing `Znth i (app l [0]) 0 = 0` plus the nonzero-prefix contract implies `i = n`

Key expected Coq bridge:
```coq
balanced_string_split_count_go balance (sublist i n l) =
  (if Z.eq_dec (balance + lr_step (Znth i l 0)) 0 then 1 else 0) +
  balanced_string_split_count_go (balance + lr_step (Znth i l 0)) (sublist (i + 1) n l)
```

Why this direction: the invariant already stores the exact suffix equation needed by the loop. The remaining proof burden is just to unfold one scanned character and normalize the `76` / non-`76` branches to `+1` / `-1`, which is cheaper and more stable in helper lemmas than inside each witness body.

Iteration 2

Phenomenon: replay compilation initially failed before the witness proofs because `goal.v` imported the short names `char_array_strategy_goal` / `char_array_strategy_proof`, and the shared examples tree contains multiple physical files with those names.

Location: [balanced_string_split_count_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/balanced_string_split_count_goal.v:21).

Repair action: add workspace-local wrappers in `original/` that re-export the `QCP_demos_LLM` strategy modules, then compile those wrappers before `goal.v`.

Key fragments:
```coq
From SimpleC.EE.QCP_demos_LLM Require Export char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.char_array_strategy_proof.
```

Why this change: it resolves the duplicate-path loader error without mutating the generated verification conditions.

Iteration 3

Phenomenon: several witness proofs failed even after the helper lemmas were in place because the first proof scripts rewrote the wrong side of the invariant equation, assumed the wrong subgoal order after `entailer!`, or relied on `balance - 1` normalizing automatically to `balance + -1`.

Location: [balanced_string_split_count_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/balanced_string_split_count_proof_manual.v:112).

Repair action:
- rewrite through the stored invariant equation (`H10`) before unfolding the one-step suffix lemma
- follow the actual `entailer!` subgoal order: suffix-spec equation first, prefix-balance equation second
- explicitly normalize `balance + -1` to `balance - 1`
- prove the exit case with local facts `Hbalance_done` and `Hcount_done` before the final `entailer!`

Key Coq fragments:
```coq
rewrite <- H10.
rewrite (go_sublist_step l n i balance H14) by lia.
replace (balance + -1) with (balance - 1) by lia.
```

Why this change: these witnesses are pure semantic bridges, not missing ownership facts. Once the list-step equalities were rewritten on the correct side and the arithmetic syntax was normalized, all six manual witnesses compiled cleanly.

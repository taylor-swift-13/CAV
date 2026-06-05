Iteration 1

Phenomenon: initial `symexec` failed with `Error: Lack of assertions in some paths for the loop!`.

Location: [annotated/verify_20260605_043229v_balanced_string_split_count.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_043229v_balanced_string_split_count.c:28), `while (1)` loop head.

Repair action: added a loop invariant summarizing the processed prefix with:
- `balance == lr_balance(sublist(0, i, l))`
- `count + balanced_string_split_count_go(balance, sublist(i, n, l)) == balanced_string_split_count_spec(l)`
- numeric bounds `0 <= count <= i` and `-i <= balance <= i`

Key fragment:
```c
/*@ Inv
      0 <= i && i <= n &&
      0 <= count && count <= i &&
      -i <= balance && balance <= i &&
      balance == lr_balance(sublist(0, i, l)) &&
      count + balanced_string_split_count_go(balance, sublist(i, n, l)) ==
      balanced_string_split_count_spec(l)
*/
```

Why this fixed it: `symexec` needs a loop-head summary on every path. The added invariant matches the scan control point and keeps exactly the suffix equation needed for the next iteration and loop exit.

Iteration 2

Phenomenon: the first generated manual proof had an impossible return witness shape: `emp |-- CharArray.full ...`.

Location: generated [balanced_string_split_count_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/balanced_string_split_count_goal.v:574) and the exit `Assert` in [annotated/verify_20260605_043229v_balanced_string_split_count.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_043229v_balanced_string_split_count.c:47).

Repair action: restored `CharArray::full(s, n + 1, app(l, cons(0, nil)))` inside the exit bridge assertion.

Key fragment:
```c
/*@ Assert
      ...
      count == balanced_string_split_count_spec(l) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Why this fixed it: `Assert` is a cut point for symbolic execution. The omitted spatial fact was not available to the return witness, so the postcondition resource had to be preserved explicitly.

Iteration 3

Phenomenon: replay compilation of `goal.v` failed before manual proof with duplicate short-name strategy modules:
`Required library char_array_strategy_goal matches several files in path`.

Location: [balanced_string_split_count_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/balanced_string_split_count_goal.v:21).

Repair action: added workspace-local wrapper modules:
- [char_array_strategy_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/original/char_array_strategy_goal.v:1)
- [char_array_strategy_proof.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/original/char_array_strategy_proof.v:1)

Key fragments:
```coq
From SimpleC.EE.QCP_demos_LLM Require Export char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.char_array_strategy_proof.
```

Why this fixed it: the generated files import short names. The wrappers give `-Q "$ORIG" ""` a unique local resolution target without modifying generated VC files.

Iteration 4

Phenomenon: manual proof compilation then failed on the semantic entailment witnesses for the loop step and exit case.

Location: [balanced_string_split_count_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/balanced_string_split_count_proof_manual.v:23).

Repair action: added local helper lemmas and proved the six manual witnesses:
- `lr_balance_app`
- `nonzero_char_implies_lt_n`
- `zero_char_implies_eq_n`
- `lr_balance_prefix_step`
- `go_sublist_step`

Key Coq bridge:
```coq
balanced_string_split_count_go balance (sublist i n l) =
  (if Z.eq_dec (balance + lr_step (Znth i l 0)) 0 then 1 else 0) +
  balanced_string_split_count_go (balance + lr_step (Znth i l 0))
    (sublist (i + 1) n l)
```

Why this fixed it: the invariant already stored the right semantic equation; the missing proof work was only the one-character unfolding of the suffix and the proof that the zero terminator forces `i = n` on exit.

Final Result: Success

Iteration 5

Phenomenon: runner audit replay still failed even after the original-round wrapper files were added, because the audit compiled `coq/generated/balanced_string_split_count_goal.v` and hit `Required library char_array_strategy_goal matches several files in path`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/logs/audit_check_coqc.log`, blocking import at [balanced_string_split_count_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/balanced_string_split_count_goal.v:21).

Repair action: added sibling wrapper sources in generated:
- [char_array_strategy_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/char_array_strategy_goal.v:1)
- [char_array_strategy_proof.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/char_array_strategy_proof.v:1)

and compiled those wrappers with the same generated logical prefix `SimpleC.EE.CAV.verify_20260605_043229v_balanced_string_split_count` before replaying:

```coq
From SimpleC.EE.QCP_demos_LLM Require Export char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.char_array_strategy_proof.
```

Why this fixed it: `goal.v` imports short strategy names from the generated directory, so disambiguation has to occur in that directory's logical namespace, not only in `original/`. Compiling the wrappers under the generated prefix produces unique local libraries that satisfy both `goal.v` and `goal_check.v` without modifying generated VC content.

Cleanup note: after replay, all generated/original/input compile byproducts were removed except the two generated wrapper `.vo` files. Those two `.vo` files are kept intentionally because the short-name strategy imports do not compile from source alone, and removing them reintroduces the duplicate-path audit failure.

Final Result: Success

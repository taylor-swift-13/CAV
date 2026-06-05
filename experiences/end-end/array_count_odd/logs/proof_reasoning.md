2026-06-05 iteration 1

Phenomenon: After the annotation repair, `/home/yangfp/CAV/C/CAV/output/verify_20260605_001431v_array_count_odd/coq/generated/array_count_odd_proof_manual.v` still contained four manual obligations: `proof_of_array_count_odd_entail_wit_2`, `proof_of_array_count_odd_entail_wit_3_1`, `proof_of_array_count_odd_entail_wit_3_2`, and `proof_of_array_count_odd_return_wit_1`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_001431v_array_count_odd/coq/generated/array_count_odd_goal.v`, theorems `array_count_odd_entail_wit_2`, `array_count_odd_entail_wit_3_1`, `array_count_odd_entail_wit_3_2`, `array_count_odd_return_wit_1`.

Repair action: Follow the same proof pattern as the verified `array_count_nonzero` case. Add one helper lemma that rewrites `array_count_odd_spec (sublist 0 (i + 1) l)` into the processed-prefix spec plus the contribution of `Znth i l 0`, then discharge the branch witnesses by `pre_process; entailer!`, a rewrite with the helper lemma, and a case split on `Z.eq_dec (Z.rem (Znth i l 0) 2) 0`. The initialization entailment should collapse under `pre_process`, and the return witness should use `i = n_pre` plus `sublist_self`.

Key proof fragment:

```coq
Lemma array_count_odd_spec_prefix_succ :
  forall l i,
    0 <= i < Zlength l ->
    array_count_odd_spec (sublist 0 (i + 1) l) =
    array_count_odd_spec (sublist 0 i l) +
    (if Z.eq_dec (Z.rem (Znth i l 0) 2) 0 then 0 else 1).
```

Why this change: The invariant already states that `count` equals the odd-count spec on the processed prefix. Each loop iteration extends that prefix by exactly one element, so the remaining proof obligation is a pure Coq fact about how the recursive spec changes on a one-element extension. Once that bridge is explicit, the branch witnesses reduce to the current `% 2` test and linear arithmetic, and the return witness becomes the standard "processed prefix equals full list at `i = n`" argument.

2026-06-05 iteration 2

Phenomenon: The first replay compilation failed before reaching any theorem body. `coqc` stopped at `/home/yangfp/CAV/C/CAV/output/verify_20260605_001431v_array_count_odd/coq/generated/array_count_odd_goal.v:21` with `Required library int_array_strategy_goal matches several files in path`, because the shared `examples/` tree exposes both `QCP_demos_LLM` and `QCP_demos_human` copies under the same short logical name.

Location: generated imports in `array_count_odd_goal.v`; duplicate `.vo` files under `/home/yangfp/CAV/C/CAV/QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/` and `/home/yangfp/CAV/C/CAV/QualifiedCProgramming/SeparationLogic/examples/QCP_demos_human/`.

Repair action: Add short-name wrapper modules under `/home/yangfp/CAV/C/CAV/output/verify_20260605_001431v_array_count_odd/original/` for every imported strategy pair: `int_array`, `uint_array`, `undef_uint_array`, and `array_shape`. Goal wrappers use `Require Export`; proof wrappers use `Require Import` plus `Include` to preserve the expected module fields for `goal_check`.

Key wrapper fragment:

```coq
From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.
```

Why this change: The generated files must stay untouched. Providing unique short-name modules in the workspace-local `original/` path lets the standard replay command keep its normal load-path order while forcing each ambiguous import to resolve to the LLM strategy library that `symexec` used.
